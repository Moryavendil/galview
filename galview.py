#!/usr/bin/env python3
"""
GalView - a read-only PDF viewer built around one job: never hide, drop or
truncate an annotation.

Design notes / why things are done the way they are:

* Annotations are harvested twice. First through PyMuPDF's normal
  ``page.annots()`` iterator, then through a raw scan of the page's /Annots
  array via the xref table. MuPDF silently skips some subtypes (Popup is the
  usual victim, but broken /Subtype entries also disappear). The raw pass
  recovers those so the sidebar count matches what is actually in the file.
* Reply annotations (/IRT) are resolved and shown nested under their parent,
  but they are still real, separate, always-visible entries.
* Nothing in the sidebar collapses, elides or hides. Every comment is a
  word-wrapped, mouse-selectable label. Overlapping annotations simply become
  adjacent cards, so stacking on the page never costs you an entry.
* Annotations without an appearance stream (/AP) are drawn by GalView itself,
  which is where Okular and Evince tend to show nothing at all.

Usage:
    python galview.py [file.pdf] [--page N]

Requires: PyMuPDF, PySide6
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field
from typing import Iterable, Optional

try:
    import pymupdf as fitz
except ImportError:  # older releases only ship the `fitz` name
    import fitz

from PySide6.QtCore import (
    QEvent,
    QObject,
    QPoint,
    QRect,
    QRectF,
    QSize,
    Qt,
    QTimer,
    Signal,
)
from PySide6.QtGui import (
    QAction,
    QColor,
    QFont,
    QGuiApplication,
    QImage,
    QKeySequence,
    QPainter,
    QPainterPath,
    QPen,
    QPixmap,
    QIcon,
    QPolygonF,
    QShortcut,
)
from PySide6.QtWidgets import (
    QAbstractScrollArea,
    QApplication,
    QCheckBox,
    QComboBox,
    QFileDialog,
    QFrame,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QMainWindow,
    QMenu,
    QMessageBox,
    QPushButton,
    QScrollArea,
    QSizePolicy,
    QSplitter,
    QToolBar,
    QToolButton,
    QVBoxLayout,
    QWidget,
)

APP_NAME = "GalView"

# ---------------------------------------------------------------------------
# palette
# ---------------------------------------------------------------------------

C_CANVAS = QColor("#4a4d55")
C_PAGE = QColor("#ffffff")
C_PAGE_EDGE = QColor("#2f3238")
C_SELECT = QColor("#1b6fd6")
C_SEARCH = QColor("#ffb020")
C_SEARCH_CUR = QColor("#ff6a00")
C_FALLBACK = QColor("#d0342c")

SHEET = """
QWidget#Sidebar { background: #f2f3f5; }
QWidget#SidebarHead { background: #e6e8ec; border-bottom: 1px solid #cfd3da; }
QScrollArea#CardScroll { background: #f2f3f5; border: none; }
QWidget#CardHost { background: #f2f3f5; }

AnnotationCard {
    background: #ffffff;
    border: 1px solid #d5d9e0;
    border-radius: 4px;
}
AnnotationCard[state="selected"] {
    background: #eaf2fd;
    border: 1px solid #1b6fd6;
}
AnnotationCard[state="match"] {
    background: #fff8e6;
    border: 1px solid #e0a92b;
}
AnnotationCard[done="true"] {
    background: #e8f6ec;
    border: 1px solid #a6d5b4;
}
AnnotationCard[done="true"][state="selected"] {
    background: #d8eee1;
    border: 1px solid #1b6fd6;
}
AnnotationCard[gone="true"] {
    background: #eef0f2;
    border: 1px dashed #c3c8d0;
}
AnnotationCard[gone="true"] QLabel { color: #a3a9b3; }
QToolButton#CardAction {
    border: none;
    background: transparent;
    padding: 0px;
}
QToolButton#CardAction:hover { background: #dfe3ea; border-radius: 3px; }
QLabel#CardHead { color: #1c1f24; }
QLabel#CardMeta { color: #6b7280; }
QLabel#CardBody { color: #14171c; }
QLabel#CardQuote { color: #8b929c; }
QLabel#CardEmpty { color: #8b929c; font-style: italic; }
QFrame#Accent { border: none; border-radius: 2px; }
QWidget#SearchBar { background: #e6e8ec; border-bottom: 1px solid #cfd3da; }
"""

# ---------------------------------------------------------------------------
# annotation model
# ---------------------------------------------------------------------------

TYPE_NAMES = {
    0: "Text", 1: "Link", 2: "FreeText", 3: "Line", 4: "Square", 5: "Circle",
    6: "Polygon", 7: "PolyLine", 8: "Highlight", 9: "Underline", 10: "Squiggly",
    11: "StrikeOut", 12: "Stamp", 13: "Caret", 14: "Ink", 15: "Popup",
    16: "FileAttachment", 17: "Sound", 18: "Movie", 19: "Widget", 20: "Screen",
    21: "PrinterMark", 22: "TrapNet", 23: "Watermark", 24: "3D", 25: "Redact",
}

FRIENDLY = {
    "Text": "Sticky note",
    "FreeText": "Text box",
    "Square": "Rectangle",
    "Circle": "Ellipse",
    "StrikeOut": "Strikeout",
    "Ink": "Freehand",
    "Popup": "Popup box",
    "FileAttachment": "Attachment",
}

MARKUP_TEXT = {"Highlight", "Underline", "Squiggly", "StrikeOut"}
STRUCTURAL = {"Popup", "Link", "Widget"}


@dataclass
class Annotation:
    uid: int
    xref: int
    page: int
    subtype: str
    author: str = ""
    content: str = ""
    subject: str = ""
    created: str = ""
    modified: str = ""
    rect: Optional[fitz.Rect] = None
    quads: list = field(default_factory=list)      # sub-rects for text markup
    quote: str = ""                # page text under a highlight/underline
    ctx_before: str = ""
    ctx_after: str = ""
    vertices: list = field(default_factory=list)   # polylines for ink/polygon
    color: Optional[QColor] = None
    has_ap: bool = True
    irt_xref: int = 0
    popup_of_xref: int = 0
    recovered: bool = False        # only found by the raw /Annots scan
    parent_uid: Optional[int] = None
    attached: bool = False         # child because of /Parent, not /IRT
    replies: list = field(default_factory=list)
    depth: int = 0
    stack: int = 1                 # annotations sharing this exact spot

    @property
    def label(self) -> str:
        return FRIENDLY.get(self.subtype, self.subtype)

    @property
    def is_reply(self) -> bool:
        return self.parent_uid is not None

    @property
    def has_comment(self) -> bool:
        return bool(self.content.strip())

    def haystack(self) -> str:
        return " ".join((self.content, self.author, self.subject,
                         self.label, self.quote)).lower()


def _date(raw: str) -> str:
    m = re.match(r"D:(\d{4})(\d{2})(\d{2})(\d{2})?(\d{2})?", raw or "")
    if not m:
        return raw or ""
    y, mo, d, h, mi = m.groups()
    stamp = f"{y}-{mo}-{d}"
    if h and mi:
        stamp += f" {h}:{mi}"
    return stamp


def _qcolor(colors: dict) -> Optional[QColor]:
    for key in ("stroke", "fill"):
        comp = (colors or {}).get(key)
        if not comp:
            continue
        try:
            if len(comp) >= 3:
                r, g, b = comp[:3]
            elif len(comp) == 1:
                r = g = b = comp[0]
            else:
                continue
            return QColor(int(r * 255), int(g * 255), int(b * 255))
        except Exception:
            continue
    return None


def _rect_from_pdf_array(text: str) -> Optional[fitz.Rect]:
    nums = re.findall(r"-?\d+\.?\d*", text or "")
    if len(nums) < 4:
        return None
    vals = [float(n) for n in nums[:4]]
    return fitz.Rect(vals).normalize()


def _xrefs_in(text: str) -> list:
    return [int(n) for n in re.findall(r"(\d+)\s+\d+\s+R", text or "")]


def _raw_annot_xrefs(doc, page) -> list:
    """Read the page's /Annots array straight out of the xref table."""
    try:
        kind, val = doc.xref_get_key(page.xref, "Annots")
    except Exception:
        return []
    if kind == "array":
        return _xrefs_in(val)
    if kind == "xref":
        try:
            target = int(val.split()[0])
        except Exception:
            return []
        try:
            return _xrefs_in(doc.xref_object(target, compressed=True))
        except Exception:
            return []
    return []


def _key(doc, xref, name):
    try:
        return doc.xref_get_key(xref, name)
    except Exception:
        return ("null", "null")


def _str_key(doc, xref, name) -> str:
    kind, val = _key(doc, xref, name)
    return val if kind == "string" else ""


def _ref_key(doc, xref, name) -> int:
    kind, val = _key(doc, xref, name)
    if kind == "xref":
        try:
            return int(val.split()[0])
        except Exception:
            return 0
    return 0


def collect_annotations(doc) -> list:
    """Every annotation in the document, live iterator plus raw recovery pass."""
    out: list = []
    uid = 0
    words_cache: dict = {}

    for pno in range(doc.page_count):
        page = doc[pno]
        seen = set()

        try:
            live = list(page.annots())
        except Exception:
            live = []

        for annot in live:
            try:
                info = annot.info or {}
                tnum, tname = annot.type[0], annot.type[1]
                subtype = tname or TYPE_NAMES.get(tnum, f"Type{tnum}")
                rec = Annotation(
                    uid=uid,
                    xref=annot.xref,
                    page=pno,
                    subtype=subtype,
                    author=info.get("title", "") or "",
                    content=info.get("content", "") or "",
                    subject=info.get("subject", "") or "",
                    created=_date(info.get("creationDate", "")),
                    modified=_date(info.get("modDate", "")),
                    rect=fitz.Rect(annot.rect).normalize(),
                    color=_qcolor(getattr(annot, "colors", None) or {}),
                    has_ap=_key(doc, annot.xref, "AP")[0] != "null",
                )
                _load_geometry(annot, rec)
                _extract_quote(page, rec, words_cache)
                rec.irt_xref = _irt_xref(doc, annot)
                if subtype == "Popup":
                    rec.popup_of_xref = _ref_key(doc, annot.xref, "Parent")
            except Exception:
                continue
            seen.add(rec.xref)
            out.append(rec)
            uid += 1

        # recovery: anything referenced by /Annots that the iterator skipped
        for xref in _raw_annot_xrefs(doc, page):
            if xref in seen or xref <= 0:
                continue
            seen.add(xref)
            sub = _key(doc, xref, "Subtype")[1].lstrip("/") or "Unknown"
            rect = _rect_from_pdf_array(_key(doc, xref, "Rect")[1])
            rec = Annotation(
                uid=uid,
                xref=xref,
                page=pno,
                subtype=sub,
                author=_str_key(doc, xref, "T"),
                content=_str_key(doc, xref, "Contents"),
                subject=_str_key(doc, xref, "Subj"),
                created=_date(_str_key(doc, xref, "CreationDate")),
                modified=_date(_str_key(doc, xref, "M")),
                rect=rect,
                has_ap=_key(doc, xref, "AP")[0] != "null",
                recovered=True,
                irt_xref=_ref_key(doc, xref, "IRT"),
                popup_of_xref=_ref_key(doc, xref, "Parent") if sub == "Popup" else 0,
            )
            out.append(rec)
            uid += 1

    _link_replies(out)
    return _ordered(out)


def _irt_xref(doc, annot) -> int:
    val = getattr(annot, "irt_xref", 0)
    if val:
        return int(val)
    kind, raw = _key(doc, annot.xref, "IRT")
    if kind == "xref":
        try:
            return int(raw.split()[0])
        except Exception:
            return 0
    return 0


def _load_geometry(annot, rec: Annotation) -> None:
    try:
        verts = annot.vertices
    except Exception:
        verts = None
    if not verts:
        return
    if rec.subtype in MARKUP_TEXT:
        flat = []
        for v in verts:
            if isinstance(v, (list, tuple)) and v and isinstance(v[0], (list, tuple)):
                flat.extend(v)
            else:
                flat.append(v)
        for i in range(0, len(flat) - 3, 4):
            pts = flat[i:i + 4]
            xs = [p[0] for p in pts]
            ys = [p[1] for p in pts]
            rec.quads.append(fitz.Rect(min(xs), min(ys), max(xs), max(ys)))
    else:
        if verts and isinstance(verts[0], (list, tuple)) and verts[0] and isinstance(verts[0][0], (list, tuple)):
            rec.vertices = [list(stroke) for stroke in verts]
        else:
            rec.vertices = [list(verts)]


def _extract_quote(page, rec: Annotation, cache: dict) -> None:
    """Pull the page text a markup annotation sits on, plus a little context."""
    if rec.subtype not in MARKUP_TEXT:
        return
    areas = rec.quads or ([rec.rect] if rec.rect else [])
    areas = [a for a in areas if a is not None and not a.is_empty]
    if not areas:
        return
    words = cache.get(page.number)
    if words is None:
        try:
            words = sorted(page.get_text("words"), key=lambda w: (w[5], w[6], w[7]))
        except Exception:
            words = []
        cache[page.number] = words
    if not words:
        return
    covered = []
    for i, w in enumerate(words):
        wr = fitz.Rect(w[:4])
        area = wr.get_area()
        if area <= 0:
            continue
        for q in areas:
            inter = wr & q
            if not inter.is_empty and inter.get_area() > 0.45 * area:
                covered.append(i)
                break
    if not covered:
        return
    lo, hi = min(covered), max(covered)
    rec.quote = " ".join(words[i][4] for i in range(lo, hi + 1)).strip()
    rec.ctx_before = " ".join(w[4] for w in words[max(0, lo - 7):lo]).strip()
    rec.ctx_after = " ".join(w[4] for w in words[hi + 1:hi + 8]).strip()


def _link_replies(records: list) -> None:
    by_xref = {r.xref: r for r in records}
    for rec in records:
        parent = by_xref.get(rec.irt_xref) if rec.irt_xref else None
        if parent is None and rec.popup_of_xref:
            parent = by_xref.get(rec.popup_of_xref)
            if parent is not None:
                rec.attached = True
        if parent is not None and parent is not rec:
            rec.parent_uid = parent.uid
            parent.replies.append(rec)
            if not rec.author:
                rec.author = parent.author
    _count_stacks(records)


def _count_stacks(records: list) -> None:
    """How many annotations share (nearly) the same anchor point on a page."""
    buckets: dict = {}
    for rec in records:
        if rec.rect is None:
            continue
        key = (rec.page, round(rec.rect.x0 / 4), round(rec.rect.y0 / 4))
        buckets.setdefault(key, []).append(rec)
    for group in buckets.values():
        for rec in group:
            rec.stack = len(group)


def _ordered(records: list) -> list:
    """Reading order per page, with replies threaded directly under parents."""
    by_uid = {r.uid: r for r in records}
    roots = [r for r in records if r.parent_uid is None or r.parent_uid not in by_uid]

    def sort_key(r: Annotation):
        y = r.rect.y0 if r.rect else 0.0
        x = r.rect.x0 if r.rect else 0.0
        return (r.page, round(y, 1), round(x, 1), r.xref)

    result: list = []
    seen: set = set()

    def walk(rec: Annotation, depth: int) -> None:
        if rec.uid in seen:
            return
        seen.add(rec.uid)
        rec.depth = depth
        result.append(rec)
        for child in sorted(rec.replies, key=lambda c: (c.created, c.xref)):
            walk(child, min(depth + 1, 3))

    for rec in sorted(roots, key=sort_key):
        walk(rec, 0)
    for rec in records:                      # cycles or orphans, never dropped
        if rec.uid not in seen:
            rec.depth = 0
            seen.add(rec.uid)
            result.append(rec)
    return result


# ---------------------------------------------------------------------------
# page canvas
# ---------------------------------------------------------------------------

GAP = 16
MARGIN = 18
CAPTION = 18


class PageCanvas(QWidget):
    annotationPicked = Signal(int)   # uid
    selectionCleared = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.doc = None
        self.annots: list = []
        self.zoom = 1.0
        self.selected_uid: Optional[int] = None
        self.hits: list = []            # (page, fitz.Rect)
        self.current_hit = -1
        self.show_outlines = True
        self._boxes: list = []          # fitz.Rect per page
        self._rects: list = []          # QRect per page in canvas space
        self._cache: dict = {}
        self._by_page: dict = {}
        self._pick_cycle: list = []
        self._pick_index = 0
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.StrongFocus)

    # -- document ---------------------------------------------------------
    def set_document(self, doc, annots: list) -> None:
        self.doc = doc
        self.annots = annots
        self._by_page = {}
        for a in annots:
            self._by_page.setdefault(a.page, []).append(a)
        self._boxes = [fitz.Rect(doc[i].rect) for i in range(doc.page_count)] if doc else []
        self._cache.clear()
        self.selected_uid = None
        self.hits = []
        self.current_hit = -1
        self.relayout()

    def set_zoom(self, zoom: float) -> None:
        zoom = max(0.1, min(8.0, zoom))
        if abs(zoom - self.zoom) < 1e-6:
            return
        self.zoom = zoom
        self._cache.clear()
        self.relayout()

    # -- layout -----------------------------------------------------------
    def relayout(self) -> None:
        self._rects = []
        if not self.doc:
            self.setMinimumSize(QSize(400, 300))
            self.resize(400, 300)
            self.update()
            return
        widths = [max(1, round(b.width * self.zoom)) for b in self._boxes]
        content_w = max(widths) if widths else 1
        total_w = content_w + 2 * MARGIN
        y = MARGIN
        for i, box in enumerate(self._boxes):
            w = widths[i]
            h = max(1, round(box.height * self.zoom))
            x = MARGIN + (content_w - w) // 2
            self._rects.append(QRect(x, y, w, h))
            y += h + CAPTION + GAP
        total_h = y - GAP + MARGIN
        self.setFixedSize(total_w, total_h)
        self.update()

    def page_rect(self, index: int) -> QRect:
        return self._rects[index] if 0 <= index < len(self._rects) else QRect()

    def doc_to_canvas(self, page: int, rect: fitz.Rect) -> QRectF:
        pr = self.page_rect(page)
        box = self._boxes[page]
        z = self.zoom
        return QRectF(
            pr.x() + (rect.x0 - box.x0) * z,
            pr.y() + (rect.y0 - box.y0) * z,
            max(1.0, rect.width * z),
            max(1.0, rect.height * z),
        )

    def canvas_to_doc(self, pos: QPoint):
        for i, pr in enumerate(self._rects):
            if pr.contains(pos):
                box = self._boxes[i]
                return i, fitz.Point(
                    box.x0 + (pos.x() - pr.x()) / self.zoom,
                    box.y0 + (pos.y() - pr.y()) / self.zoom,
                )
        return None, None

    def page_at_viewport_y(self, y: int) -> int:
        for i, pr in enumerate(self._rects):
            if pr.top() <= y <= pr.bottom() + CAPTION + GAP:
                return i
        if self._rects and y > self._rects[-1].bottom():
            return len(self._rects) - 1
        return 0

    # -- rendering --------------------------------------------------------
    def _pixmap(self, index: int) -> Optional[QPixmap]:
        key = (index, round(self.zoom, 4))
        hit = self._cache.get(key)
        if hit is not None:
            return hit
        try:
            dpr = self.devicePixelRatioF() or 1.0
            mat = fitz.Matrix(self.zoom * dpr, self.zoom * dpr)
            pix = self.doc[index].get_pixmap(matrix=mat, alpha=False, annots=True)
            img = QImage(pix.samples, pix.width, pix.height, pix.stride,
                         QImage.Format_RGB888).copy()
            qpm = QPixmap.fromImage(img)
            qpm.setDevicePixelRatio(dpr)
        except Exception:
            return None
        if len(self._cache) > 12:
            for k in list(self._cache)[:6]:
                self._cache.pop(k, None)
        self._cache[key] = qpm
        return qpm

    def paintEvent(self, event) -> None:
        p = QPainter(self)
        p.fillRect(event.rect(), C_CANVAS)
        if not self.doc:
            p.setPen(QColor("#c8ccd4"))
            f = p.font(); f.setPointSize(13); p.setFont(f)
            p.drawText(self.rect(), Qt.AlignCenter,
                       "Open a PDF to read its annotations  (Ctrl+O)")
            return
        p.setRenderHint(QPainter.Antialiasing, True)
        for i, pr in enumerate(self._rects):
            if not pr.intersects(event.rect().adjusted(-40, -400, 40, 400)):
                continue
            p.fillRect(pr, C_PAGE)
            pm = self._pixmap(i)
            if pm is not None:
                p.drawPixmap(pr.topLeft(), pm)
            p.setPen(QPen(C_PAGE_EDGE, 1))
            p.drawRect(pr.adjusted(0, 0, -1, -1))
            self._paint_overlays(p, i)
            self._paint_caption(p, i, pr)
        p.end()

    def _paint_caption(self, p: QPainter, index: int, pr: QRect) -> None:
        p.save()
        f = p.font(); f.setPointSize(8); p.setFont(f)
        p.setPen(QColor("#c9ccd3"))
        n = len(self._by_page.get(index, []))
        text = f"Page {index + 1} of {len(self._rects)}"
        if n:
            text += f"   ·   {n} annotation{'s' if n != 1 else ''}"
        p.drawText(QRect(pr.x(), pr.bottom() + 3, pr.width(), CAPTION - 4),
                   Qt.AlignHCenter | Qt.AlignTop, text)
        p.restore()

    def _paint_overlays(self, p: QPainter, index: int) -> None:
        badges: dict = {}
        for rec in self._by_page.get(index, []):
            if rec.rect is None or rec.rect.is_empty:
                continue
            needs_fallback = not rec.has_ap and rec.subtype not in STRUCTURAL
            if needs_fallback:
                self._draw_fallback(p, rec)
            elif self.show_outlines and rec.subtype not in STRUCTURAL:
                self._draw_outline(p, rec)
            if rec.stack > 1 and rec.subtype not in STRUCTURAL:
                key = (round(rec.rect.x0 / 4), round(rec.rect.y0 / 4))
                badges[key] = (rec, rec.stack)

        for rec, count in badges.values():
            self._draw_stack_badge(p, rec, count)

        for hi, (pno, rect) in enumerate(self.hits):
            if pno != index:
                continue
            r = self.doc_to_canvas(pno, rect)
            cur = hi == self.current_hit
            col = QColor(C_SEARCH_CUR if cur else C_SEARCH)
            col.setAlpha(150 if cur else 105)
            p.fillRect(r, col)
            if cur:
                p.setPen(QPen(QColor("#8a3a00"), 1.5))
                p.drawRect(r)

        sel = self.selected()
        if sel is not None and sel.page == index and sel.rect is not None:
            r = self.doc_to_canvas(index, sel.rect)
            if r.width() < 6 or r.height() < 6:
                r = r.adjusted(-6, -6, 6, 6)
            glow = QColor(C_SELECT); glow.setAlpha(38)
            p.fillRect(r, glow)
            p.setPen(QPen(C_SELECT, 2.5))
            p.drawRect(r)
            p.setPen(QPen(QColor("#ffffff"), 1))
            p.drawRect(r.adjusted(-1.5, -1.5, 1.5, 1.5))

    def _draw_outline(self, p: QPainter, rec: Annotation) -> None:
        col = QColor(rec.color or QColor("#7c8798"))
        col.setAlpha(150)
        pen = QPen(col, 1, Qt.DotLine)
        p.setPen(pen)
        p.setBrush(Qt.NoBrush)
        p.drawRect(self.doc_to_canvas(rec.page, rec.rect))

    def _draw_fallback(self, p: QPainter, rec: Annotation) -> None:
        """Draw annotations the file gives us no appearance stream for."""
        col = QColor(rec.color or C_FALLBACK)
        r = self.doc_to_canvas(rec.page, rec.rect)
        p.save()
        if rec.subtype == "Highlight":
            fill = QColor(col); fill.setAlpha(90)
            for q in (rec.quads or [rec.rect]):
                p.fillRect(self.doc_to_canvas(rec.page, q), fill)
        elif rec.subtype in ("Underline", "Squiggly", "StrikeOut"):
            p.setPen(QPen(col, 1.6))
            for q in (rec.quads or [rec.rect]):
                qr = self.doc_to_canvas(rec.page, q)
                y = qr.center().y() if rec.subtype == "StrikeOut" else qr.bottom() - 1
                p.drawLine(qr.left(), y, qr.right(), y)
        elif rec.subtype == "Square":
            p.setPen(QPen(col, 2))
            p.setBrush(Qt.NoBrush)
            p.drawRect(r)
        elif rec.subtype == "Circle":
            p.setPen(QPen(col, 2))
            p.setBrush(Qt.NoBrush)
            p.drawEllipse(r)
        elif rec.subtype in ("Ink", "Polygon", "PolyLine", "Line") and rec.vertices:
            p.setPen(QPen(col, 1.8, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
            p.setBrush(Qt.NoBrush)
            for stroke in rec.vertices:
                poly = QPolygonF([
                    self.doc_to_canvas(rec.page, fitz.Rect(x, y, x, y)).topLeft()
                    for x, y in stroke
                ])
                if rec.subtype == "Polygon":
                    p.drawPolygon(poly)
                else:
                    p.drawPolyline(poly)
        elif rec.subtype == "Text":
            self._draw_note_icon(p, r, col)
        else:
            p.setPen(QPen(col, 1.4, Qt.DashLine))
            p.setBrush(Qt.NoBrush)
            p.drawRect(r)
        p.restore()

    def _draw_stack_badge(self, p: QPainter, rec: Annotation, count: int) -> None:
        """Tell the reader that more than one annotation lives under this spot."""
        r = self.doc_to_canvas(rec.page, rec.rect)
        d = 15.0
        box = QRectF(r.right() - d / 2, r.top() - d / 2, d, d)
        p.save()
        p.setPen(QPen(QColor("#ffffff"), 1.5))
        p.setBrush(C_SELECT)
        p.drawEllipse(box)
        f = p.font(); f.setPointSizeF(8.0); f.setBold(True); p.setFont(f)
        p.setPen(QColor("#ffffff"))
        p.drawText(box, Qt.AlignCenter, str(min(count, 99)))
        p.restore()

    def _draw_note_icon(self, p: QPainter, r: QRectF, col: QColor) -> None:
        side = max(14.0, min(r.width() or 18, 22.0))
        box = QRectF(r.left(), r.top(), side, side)
        path = QPainterPath()
        path.addRoundedRect(box, 3, 3)
        fill = QColor(col); fill.setAlpha(220)
        p.fillPath(path, fill)
        p.setPen(QPen(QColor("#00000060"), 1))
        p.drawPath(path)
        p.setPen(QPen(QColor("#ffffff"), 1.2))
        for k in (0.32, 0.5, 0.68):
            y = box.top() + box.height() * k
            p.drawLine(box.left() + 3.5, y, box.right() - 3.5, y)

    # -- interaction ------------------------------------------------------
    def selected(self) -> Optional[Annotation]:
        if self.selected_uid is None:
            return None
        for a in self.annots:
            if a.uid == self.selected_uid:
                return a
        return None

    def select(self, uid: Optional[int]) -> None:
        self.selected_uid = uid
        self.update()

    def mousePressEvent(self, event) -> None:
        if event.button() != Qt.LeftButton:
            return super().mousePressEvent(event)
        pos = event.position().toPoint()
        page, pt = self.canvas_to_doc(pos)
        if page is None:
            self._pick_cycle = []
            if self.selected_uid is not None:
                self.selectionCleared.emit()
            return
        pad = 3.0 / max(self.zoom, 0.01)
        under = [
            a for a in self._by_page.get(page, [])
            if a.rect is not None
            and fitz.Rect(a.rect.x0 - pad, a.rect.y0 - pad,
                          a.rect.x1 + pad, a.rect.y1 + pad).contains(pt)
        ]
        if not under:
            self._pick_cycle = []
            self._pick_index = 0
            if self.selected_uid is not None:
                self.selectionCleared.emit()
            return
        # smallest first, so a note stacked on a big box stays reachable
        under.sort(key=lambda a: a.rect.width * a.rect.height)
        uids = [a.uid for a in under]
        if uids == self._pick_cycle:
            self._pick_index = (self._pick_index + 1) % len(uids)
        else:
            self._pick_cycle = uids
            self._pick_index = 0
        self.annotationPicked.emit(uids[self._pick_index])


class PageView(QScrollArea):
    pageChanged = Signal(int)
    zoomStepped = Signal(int)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.canvas = PageCanvas(self)
        self.setWidget(self.canvas)
        self.setWidgetResizable(False)
        self.setAlignment(Qt.AlignCenter)
        self.viewport().setStyleSheet(f"background: {C_CANVAS.name()};")
        self.setSizeAdjustPolicy(QAbstractScrollArea.AdjustIgnored)
        self._last_page = -1
        self.verticalScrollBar().valueChanged.connect(self._report_page)

    def _report_page(self) -> None:
        if not self.canvas.doc:
            return
        y = self.verticalScrollBar().value() + self.viewport().height() // 3
        page = self.canvas.page_at_viewport_y(y)
        if page != self._last_page:
            self._last_page = page
            self.pageChanged.emit(page)

    def goto_page(self, index: int) -> None:
        pr = self.canvas.page_rect(index)
        if pr.isNull():
            return
        self.verticalScrollBar().setValue(max(0, pr.top() - MARGIN))
        self.horizontalScrollBar().setValue(max(0, pr.left() - MARGIN))

    def reveal(self, page: int, rect: fitz.Rect) -> None:
        r = self.canvas.doc_to_canvas(page, rect)
        vp = self.viewport()
        cx = int(r.center().x())
        cy = int(r.center().y())
        self.ensureVisible(cx, cy, vp.width() // 2 - 30, vp.height() // 2 - 30)

    def wheelEvent(self, event) -> None:
        if event.modifiers() & Qt.ControlModifier:
            self.zoomStepped.emit(1 if event.angleDelta().y() > 0 else -1)
            event.accept()
            return
        super().wheelEvent(event)

    def resizeEvent(self, event) -> None:
        super().resizeEvent(event)
        self._report_page()


# ---------------------------------------------------------------------------
# sidebar
# ---------------------------------------------------------------------------

class AnnotationCard(QFrame):
    activated = Signal(int)
    validateToggled = Signal(int)
    dismissToggled = Signal(int)

    def __init__(self, rec: Annotation, parent=None):
        super().__init__(parent)
        self.rec = rec
        self.setProperty("state", "normal")
        self.setSizePolicy(_wrap_policy(QSizePolicy.Preferred))
        self.setCursor(Qt.PointingHandCursor)

        outer = QHBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)

        accent = QFrame(self)
        accent.setObjectName("Accent")
        accent.setFixedWidth(4)
        col = rec.color or QColor("#98a2b3")
        accent.setStyleSheet(f"background: {col.name()};")
        outer.addWidget(accent)

        col_layout = QVBoxLayout()
        col_layout.setContentsMargins(10, 8, 10, 9)
        col_layout.setSpacing(3)
        outer.addLayout(col_layout, 1)

        head = QLabel(self._head_text())
        head.setObjectName("CardHead")
        head.setWordWrap(True)
        head.setSizePolicy(_wrap_policy())
        head.setTextFormat(Qt.RichText)

        head_row = QHBoxLayout()
        head_row.setContentsMargins(0, 0, 0, 0)
        head_row.setSpacing(2)
        head_row.addWidget(head, 1)

        self.btn_done = QToolButton(self)
        self.btn_done.setObjectName("CardAction")
        self.btn_done.setAutoRaise(True)
        self.btn_done.setIconSize(QSize(15, 15))
        self.btn_done.setFixedSize(21, 21)
        self.btn_done.clicked.connect(lambda: self.validateToggled.emit(rec.uid))
        head_row.addWidget(self.btn_done, 0, Qt.AlignTop)

        self.btn_bin = QToolButton(self)
        self.btn_bin.setObjectName("CardAction")
        self.btn_bin.setAutoRaise(True)
        self.btn_bin.setIconSize(QSize(15, 15))
        self.btn_bin.setFixedSize(21, 21)
        self.btn_bin.clicked.connect(lambda: self.dismissToggled.emit(rec.uid))
        head_row.addWidget(self.btn_bin, 0, Qt.AlignTop)

        col_layout.addLayout(head_row)
        self.set_marks(False, False)

        self.quote_label = None
        if rec.quote:
            quote = QLabel(self._quote_html())
            quote.setObjectName("CardQuote")
            quote.setWordWrap(True)
            quote.setTextFormat(Qt.RichText)
            quote.setTextInteractionFlags(
                Qt.TextSelectableByMouse | Qt.TextSelectableByKeyboard)
            quote.setSizePolicy(_wrap_policy())
            quote.setMinimumWidth(60)
            qf = quote.font(); qf.setPointSize(max(7, qf.pointSize() - 1))
            quote.setFont(qf)
            quote.installEventFilter(self)
            col_layout.addWidget(quote)
            self.quote_label = quote

        text = (rec.content or "").strip()
        body = QLabel(text if text else "No comment text on this annotation")
        body.setObjectName("CardBody" if text else "CardEmpty")
        body.setWordWrap(True)
        body.setTextFormat(Qt.PlainText)
        body.setTextInteractionFlags(
            Qt.TextSelectableByMouse | Qt.TextSelectableByKeyboard)
        body.setSizePolicy(_wrap_policy())
        body.setMinimumWidth(60)
        body.installEventFilter(self)
        f = body.font(); f.setPointSize(f.pointSize() + 1); body.setFont(f)
        col_layout.addWidget(body)
        self.body = body

        meta_bits = [b for b in (rec.modified or rec.created,
                                 rec.subject,
                                 f"xref {rec.xref}") if b]
        if rec.stack > 1:
            meta_bits.append(f"{rec.stack} annotations share this spot")
        if not rec.has_ap:
            meta_bits.append("no appearance stream — drawn by GalView")
        if rec.recovered:
            meta_bits.append("recovered from /Annots")
        meta = QLabel("  ·  ".join(meta_bits))
        meta.setObjectName("CardMeta")
        meta.setWordWrap(True)
        meta.setSizePolicy(_wrap_policy())
        mf = meta.font(); mf.setPointSize(max(7, mf.pointSize() - 1)); meta.setFont(mf)
        meta.setTextInteractionFlags(Qt.TextSelectableByMouse)
        meta.installEventFilter(self)
        col_layout.addWidget(meta)

        head.installEventFilter(self)
        self.setContextMenuPolicy(Qt.CustomContextMenu)
        self.customContextMenuRequested.connect(self._menu)

    def _quote_html(self) -> str:
        rec = self.rec
        base = rec.color or QColor("#ffd43b")
        tint = QColor(*[int(255 - (255 - c) * 0.45)
                        for c in (base.red(), base.green(), base.blue())]).name()
        before = f"…{_esc(rec.ctx_before)} " if rec.ctx_before else ""
        after = f" {_esc(rec.ctx_after)}…" if rec.ctx_after else ""
        return (f"<span style='color:#98a0ab'>{before}</span>"
                f"<span style='background-color:{tint}; color:#14171c'>"
                f"{_esc(rec.quote)}</span>"
                f"<span style='color:#98a0ab'>{after}</span>")

    def _head_text(self) -> str:
        rec = self.rec
        author = rec.author.strip() or "Unknown author"
        if rec.attached:
            prefix = "belongs to the entry above · "
        elif rec.is_reply:
            prefix = "reply · "
        else:
            prefix = ""
        return (f"<b>{_esc(rec.label)}</b> &nbsp;<span style='color:#6b7280'>"
                f"{prefix}p.{rec.page + 1} · {_esc(author)}</span>")

    def eventFilter(self, obj: QObject, event: QEvent) -> bool:
        # let the label keep its own text selection, but still register the click
        if event.type() == QEvent.MouseButtonPress and event.button() == Qt.LeftButton:
            self.activated.emit(self.rec.uid)
        return False

    def mousePressEvent(self, event) -> None:
        if event.button() == Qt.LeftButton:
            self.activated.emit(self.rec.uid)
        super().mousePressEvent(event)

    def set_marks(self, done: bool, gone: bool) -> None:
        self.btn_done.setIcon(_icon("uncheck" if done else "check"))
        self.btn_done.setToolTip("Clear the reviewed mark" if done
                                 else "Mark this annotation reviewed")
        self.btn_bin.setIcon(_icon("restore" if gone else "bin"))
        self.btn_bin.setToolTip("Put this annotation back in the list" if gone
                                else "Dismiss from the list (the PDF is not changed)")
        for name, value in (("done", done), ("gone", gone)):
            if self.property(name) != ("true" if value else "false"):
                self.setProperty(name, "true" if value else "false")
                self.style().unpolish(self)
                self.style().polish(self)

    def set_state(self, state: str) -> None:
        if self.property("state") == state:
            return
        self.setProperty("state", state)
        self.style().unpolish(self)
        self.style().polish(self)

    def plain_text(self) -> str:
        rec = self.rec
        who = rec.author or "Unknown author"
        lines = [f"[p.{rec.page + 1}] {rec.label} — {who}"]
        if rec.quote:
            lines.append(f'  “{rec.quote}”')
        lines.append(rec.content.strip() or "(no comment text)")
        return "\n".join(lines)

    def _menu(self, pos) -> None:
        menu = QMenu(self)
        act_one = menu.addAction("Copy this comment")
        act_sel = menu.addAction("Copy selected text")
        act_sel.setEnabled(bool(self.body.selectedText()))
        chosen = menu.exec(self.mapToGlobal(pos))
        cb = QGuiApplication.clipboard()
        if chosen is act_one:
            cb.setText(self.plain_text())
        elif chosen is act_sel:
            cb.setText(self.body.selectedText())


_ICONS: dict = {}


def _icon(kind: str) -> QIcon:
    """Small painted glyphs, so the app stays a single file with no assets."""
    if kind in _ICONS:
        return _ICONS[kind]
    pm = QPixmap(36, 36)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing, True)
    if kind == "bin":
        p.setPen(QPen(QColor("#8a929e"), 2.6, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        p.drawLine(8, 11, 28, 11)
        p.drawLine(14, 11, 14, 8); p.drawLine(14, 8, 22, 8); p.drawLine(22, 8, 22, 11)
        p.drawLine(11, 11, 12.5, 29); p.drawLine(25, 11, 23.5, 29)
        p.drawLine(12.5, 29, 23.5, 29)
        p.setPen(QPen(QColor("#8a929e"), 2.0, Qt.SolidLine, Qt.RoundCap))
        p.drawLine(15.5, 15, 16.2, 25); p.drawLine(20.5, 15, 19.8, 25)
    elif kind == "restore":
        p.setPen(QPen(QColor("#5b78a8"), 2.8, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        p.drawArc(8, 8, 20, 20, 40 * 16, 280 * 16)
        p.setBrush(QColor("#5b78a8")); p.setPen(Qt.NoPen)
        p.drawPolygon(QPolygonF([QPoint(26, 4), QPoint(29, 14), QPoint(19, 12)]))
    elif kind == "check":
        p.setPen(QPen(QColor("#2f9e5b"), 3.4, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
        p.drawLine(8, 19, 15, 26); p.drawLine(15, 26, 28, 9)
    elif kind == "uncheck":
        p.setPen(QPen(QColor("#77808d"), 3.0, Qt.SolidLine, Qt.RoundCap))
        p.drawLine(10, 10, 26, 26); p.drawLine(26, 10, 10, 26)
    p.end()
    _ICONS[kind] = QIcon(pm)
    return _ICONS[kind]


def _wrap_policy(horizontal=QSizePolicy.Ignored) -> QSizePolicy:
    """Word-wrapped widgets must advertise heightForWidth, and must use a
    shrinkable vertical policy. With QSizePolicy.Minimum, Qt floors the
    layout at each label's unwrapped size hint, so the scroll range stays
    huge no matter how many cards are hidden."""
    sp = QSizePolicy(horizontal, QSizePolicy.Preferred)
    sp.setHeightForWidth(True)
    return sp


def _esc(text: str) -> str:
    return (text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


class Sidebar(QWidget):
    annotationChosen = Signal(int)
    marksChanged = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("Sidebar")
        self.cards: dict = {}
        self.records: list = []
        self.validated: set = set()
        self.dismissed: set = set()
        self._filter = ""
        self._selected: Optional[int] = None

        root = QVBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        head = QWidget(); head.setObjectName("SidebarHead")
        hl = QVBoxLayout(head)
        hl.setContentsMargins(10, 8, 10, 8)
        hl.setSpacing(6)

        row = QHBoxLayout(); row.setSpacing(8)
        self.count = QLabel("No document open")
        cf = self.count.font(); cf.setBold(True); self.count.setFont(cf)
        row.addWidget(self.count, 1)
        self.copy_all = QPushButton("Copy all")
        self.copy_all.setToolTip("Copy every annotation in this list as plain text")
        self.copy_all.clicked.connect(self._copy_all)
        row.addWidget(self.copy_all)
        hl.addLayout(row)

        self.hide_struct = QCheckBox("Hide popup, link and form entries")
        self.hide_struct.setChecked(True)
        self.hide_struct.setToolTip(
            "Popup boxes, links and form fields carry no comment of their own. "
            "Clear this to list every object in the file.")
        self.hide_struct.toggled.connect(lambda _: self.apply_filter(self._filter))
        hl.addWidget(self.hide_struct)

        self.show_gone = QCheckBox("Show dismissed entries")
        self.show_gone.setToolTip(
            "Dismissing only removes an entry from this list. "
            "Nothing is ever written to the PDF.")
        self.show_gone.setVisible(False)
        self.show_gone.toggled.connect(lambda _: self.apply_filter(self._filter))
        hl.addWidget(self.show_gone)
        root.addWidget(head)

        self.scroll = QScrollArea()
        self.scroll.setObjectName("CardScroll")
        self.scroll.setWidgetResizable(True)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.host = QWidget(); self.host.setObjectName("CardHost")
        self.vbox = QVBoxLayout(self.host)
        self.vbox.setContentsMargins(8, 8, 8, 8)
        self.vbox.setSpacing(6)
        self.vbox.addStretch(1)
        self.scroll.setWidget(self.host)
        root.addWidget(self.scroll, 1)

        self.empty = QLabel("")
        self.empty.setAlignment(Qt.AlignCenter)
        self.empty.setWordWrap(True)
        self.empty.setStyleSheet("color:#7a828e; padding: 24px;")
        self.vbox.insertWidget(0, self.empty)

    # -- population -------------------------------------------------------
    def set_records(self, records: list) -> None:
        for card in self.cards.values():
            card.setParent(None)
            card.deleteLater()
        self.cards.clear()
        self.records = records
        self.validated = set()
        self.dismissed = set()
        for rec in records:
            wrapper = QWidget(self.host)
            wrapper.setSizePolicy(_wrap_policy(QSizePolicy.Preferred))
            wl = QHBoxLayout(wrapper)
            wl.setContentsMargins(rec.depth * 18, 0, 0, 0)
            wl.setSpacing(0)
            card = AnnotationCard(rec, wrapper)
            card.activated.connect(self.annotationChosen.emit)
            card.validateToggled.connect(self._toggle_validated)
            card.dismissToggled.connect(self._toggle_dismissed)
            wl.addWidget(card)
            self.cards[rec.uid] = wrapper
            wrapper.card = card
            self.vbox.insertWidget(self.vbox.count() - 1, wrapper)
        self.apply_filter(self._filter)

    def _update_count(self, shown: int, comments: int) -> None:
        total = len(self.records)
        if not total:
            self.count.setText("No annotations in this document")
            return
        all_comments = sum(1 for r in self.records if r.has_comment)
        if comments == all_comments and shown == total:
            tail = f"  [{all_comments} comment{'s' if all_comments != 1 else ''}]"
        else:
            tail = f"  [{comments}/{all_comments} comments]"
        head = (f"{total} annotation{'s' if total != 1 else ''}"
                if shown == total else f"{shown} of {total} annotations shown")
        marks = []
        if self.validated:
            marks.append(f"{len(self.validated)} reviewed")
        if self.dismissed:
            marks.append(f"{len(self.dismissed)} dismissed")
        suffix = "  ·  " + ", ".join(marks) if marks else ""
        self.count.setText(head + tail + suffix)
        self.show_gone.setVisible(bool(self.dismissed))

    def apply_filter(self, term: str) -> None:
        self._filter = term or ""
        needle = self._filter.strip().lower()
        shown = 0
        comments = 0
        for rec in self.records:
            wrapper = self.cards.get(rec.uid)
            if wrapper is None:
                continue
            visible = True
            if self.hide_struct.isChecked() and rec.subtype in STRUCTURAL and not rec.content.strip():
                visible = False
            if rec.uid in self.dismissed and not self.show_gone.isChecked():
                visible = False
            wrapper.setVisible(visible)
            wrapper.card.set_marks(rec.uid in self.validated,
                                   rec.uid in self.dismissed)
            if visible:
                shown += 1
                if rec.has_comment and rec.uid not in self.dismissed:
                    comments += 1
                match = bool(needle) and needle in rec.haystack()
                state = "selected" if rec.uid == self._selected else ("match" if match else "normal")
                wrapper.card.set_state(state)
        self._update_count(shown, comments)
        self._resize_host()
        if not shown:
            self.empty.setText(
                "Nothing to show here."
                if not self.records else
                "No annotation matches the current filter.")
            self.empty.show()
        else:
            self.empty.hide()

    def _toggle_validated(self, uid: int) -> None:
        self.validated.symmetric_difference_update({uid})
        self.apply_filter(self._filter)
        self.marksChanged.emit()

    def _toggle_dismissed(self, uid: int) -> None:
        self.dismissed.symmetric_difference_update({uid})
        if uid in self.dismissed and uid == self._selected:
            self._selected = None
        self.apply_filter(self._filter)
        self.marksChanged.emit()

    def set_marks(self, validated: set, dismissed: set) -> None:
        self.validated = set(validated)
        self.dismissed = set(dismissed)
        self.apply_filter(self._filter)

    def _resize_host(self) -> None:
        """Hidden cards must give their space back, or the scrollbar lies.
        adjustSize() is wrong here: it measures heightForWidth at the host's
        own narrow size hint, which leaves a screenful of dead space."""
        self.vbox.invalidate()
        self.vbox.activate()
        self.host.updateGeometry()
        width = max(self.scroll.viewport().width(), 1)
        if self.vbox.hasHeightForWidth():
            height = self.vbox.totalHeightForWidth(width)
        else:
            height = self.vbox.totalSizeHint().height()
        self.host.resize(width, max(1, height))

    def select(self, uid: Optional[int], scroll: bool = True) -> None:
        self._selected = uid
        self.apply_filter(self._filter)
        if uid is None or not scroll:
            return
        wrapper = self.cards.get(uid)
        if wrapper is not None and wrapper.isVisible():
            self.scroll.ensureWidgetVisible(wrapper, 0, 60)

    def resizeEvent(self, event) -> None:
        super().resizeEvent(event)
        QTimer.singleShot(0, self._resize_host)

    def matches(self, term: str) -> int:
        needle = (term or "").strip().lower()
        if not needle:
            return 0
        return sum(1 for r in self.records if needle in r.haystack())

    def _copy_all(self) -> None:
        chunks = []
        for rec in self.records:
            wrapper = self.cards.get(rec.uid)
            if wrapper is None or not wrapper.isVisible():
                continue
            if rec.uid in self.dismissed:
                continue
            mark = "[reviewed] " if rec.uid in self.validated else ""
            chunks.append("    " * rec.depth + mark + wrapper.card.plain_text())
        QGuiApplication.clipboard().setText("\n\n".join(chunks))


# ---------------------------------------------------------------------------
# search bar
# ---------------------------------------------------------------------------

class SearchBar(QWidget):
    queryChanged = Signal(str)
    stepped = Signal(int)
    closed = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("SearchBar")
        lay = QHBoxLayout(self)
        lay.setContentsMargins(10, 6, 10, 6)
        lay.setSpacing(8)

        self.field = QLineEdit()
        self.field.setPlaceholderText("Find in page text and annotations")
        self.field.setClearButtonEnabled(True)
        self.field.returnPressed.connect(lambda: self.stepped.emit(1))
        self.field.textChanged.connect(self.queryChanged.emit)
        lay.addWidget(self.field, 1)

        prev = QPushButton("Previous"); prev.clicked.connect(lambda: self.stepped.emit(-1))
        nxt = QPushButton("Next"); nxt.clicked.connect(lambda: self.stepped.emit(1))
        lay.addWidget(prev); lay.addWidget(nxt)

        self.status = QLabel("")
        self.status.setMinimumWidth(190)
        lay.addWidget(self.status)

        close = QPushButton("Close"); close.clicked.connect(self.closed.emit)
        lay.addWidget(close)

    def keyPressEvent(self, event) -> None:
        if event.key() == Qt.Key_Escape:
            self.closed.emit()
            return
        super().keyPressEvent(event)


# ---------------------------------------------------------------------------
# main window
# ---------------------------------------------------------------------------

ZOOMS = [0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 3.0, 4.0]


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.doc = None
        self.path = ""
        self.records: list = []
        self.hits: list = []
        self.hit_index = -1
        self.fit_width = False
        self._doc_summary = "Ready"
        self.remember_marks = True

        self.setWindowTitle(APP_NAME)
        self.resize(1360, 900)
        self.setStyleSheet(SHEET)

        self.view = PageView()
        self.sidebar = Sidebar()
        self.search = SearchBar()
        self.search.hide()

        splitter = QSplitter(Qt.Horizontal)
        splitter.addWidget(self.view)
        splitter.addWidget(self.sidebar)
        splitter.setStretchFactor(0, 3)
        splitter.setStretchFactor(1, 2)
        splitter.setSizes([840, 480])
        splitter.setChildrenCollapsible(False)

        central = QWidget()
        cl = QVBoxLayout(central)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.setSpacing(0)
        cl.addWidget(self.search)
        cl.addWidget(splitter, 1)
        self.setCentralWidget(central)

        self._build_toolbar()
        self.statusBar().showMessage("Ready")

        self.sidebar.annotationChosen.connect(self.focus_annotation)
        self.sidebar.marksChanged.connect(self._save_marks)
        self.view.canvas.annotationPicked.connect(self.focus_annotation)
        self.view.canvas.selectionCleared.connect(self.clear_annotation)
        self.view.pageChanged.connect(self._page_indicator)
        self.view.zoomStepped.connect(self.step_zoom)
        self.search.queryChanged.connect(self._search_changed)
        self.search.stepped.connect(self.step_hit)
        self.search.closed.connect(self.close_search)

        self._shortcuts()

    # -- chrome -----------------------------------------------------------
    def _build_toolbar(self) -> None:
        bar = QToolBar("Main")
        bar.setMovable(False)
        self.addToolBar(bar)

        act_open = QAction("Open PDF", self)
        act_open.setShortcut(QKeySequence.Open)
        act_open.triggered.connect(self.open_dialog)
        bar.addAction(act_open)
        bar.addSeparator()

        self.act_prev = QAction("Previous page", self)
        self.act_prev.triggered.connect(lambda: self.jump_page(self.current_page() - 1))
        bar.addAction(self.act_prev)

        self.page_edit = QLineEdit()
        self.page_edit.setFixedWidth(58)
        self.page_edit.setAlignment(Qt.AlignCenter)
        self.page_edit.returnPressed.connect(self._page_entered)
        bar.addWidget(self.page_edit)

        self.page_total = QLabel(" of 0 ")
        bar.addWidget(self.page_total)

        self.act_next = QAction("Next page", self)
        self.act_next.triggered.connect(lambda: self.jump_page(self.current_page() + 1))
        bar.addAction(self.act_next)
        bar.addSeparator()

        act_out = QAction("Zoom out", self); act_out.triggered.connect(lambda: self.step_zoom(-1))
        bar.addAction(act_out)
        self.zoom_box = QComboBox()
        self.zoom_box.setEditable(False)
        for z in ZOOMS:
            self.zoom_box.addItem(f"{int(z * 100)}%", z)
        self.zoom_box.addItem("Fit width", "fit")
        self.zoom_box.setCurrentIndex(ZOOMS.index(1.0))
        self.zoom_box.activated.connect(self._zoom_chosen)
        bar.addWidget(self.zoom_box)
        act_in = QAction("Zoom in", self); act_in.triggered.connect(lambda: self.step_zoom(1))
        bar.addAction(act_in)
        bar.addSeparator()

        act_find = QAction("Find", self)
        act_find.setShortcut(QKeySequence.Find)
        act_find.triggered.connect(self.open_search)
        bar.addAction(act_find)

        self.act_outlines = QAction("Show annotation outlines", self)
        self.act_outlines.setCheckable(True)
        self.act_outlines.setChecked(True)
        self.act_outlines.setToolTip(
            "Draw a dotted border around every annotation so shape-linked ones are findable")
        self.act_outlines.toggled.connect(self._toggle_outlines)
        bar.addAction(self.act_outlines)

    def _shortcuts(self) -> None:
        def sc(seq, fn):
            s = QShortcut(QKeySequence(seq), self)
            s.activated.connect(fn)
            return s

        sc("Ctrl++", lambda: self.step_zoom(1))
        sc("Ctrl+=", lambda: self.step_zoom(1))
        sc("Ctrl+-", lambda: self.step_zoom(-1))
        sc("Ctrl+0", lambda: self.set_zoom(1.0))
        sc("Ctrl+PgDown", lambda: self.jump_page(self.current_page() + 1))
        sc("Ctrl+PgUp", lambda: self.jump_page(self.current_page() - 1))
        sc("F3", lambda: self.step_hit(1))
        sc("Shift+F3", lambda: self.step_hit(-1))
        sc("Escape", self.close_search)

    # -- document ---------------------------------------------------------
    def open_dialog(self) -> None:
        path, _ = QFileDialog.getOpenFileName(
            self, "Open PDF", "", "PDF documents (*.pdf);;All files (*)")
        if path:
            self.load(path)

    def load(self, path: str) -> bool:
        try:
            doc = fitz.open(path)
        except Exception as exc:
            QMessageBox.critical(self, "Cannot open file",
                                 f"GalView could not read this file.\n\n{exc}")
            return False
        if doc.needs_pass:
            QMessageBox.critical(self, "Encrypted document",
                                 "This PDF is password protected. GalView opens "
                                 "unprotected files only.")
            return False
        self.doc = doc
        self.path = path
        self.records = collect_annotations(doc)
        self.view.canvas.set_document(doc, self.records)
        self.sidebar.set_records(self.records)
        self._load_marks()
        self.hits = []
        self.hit_index = -1
        self.view.canvas.hits = []
        self.search.field.clear()
        self.page_total.setText(f" of {doc.page_count} ")
        self._page_indicator(0)
        self.view.goto_page(0)
        name = path.rsplit("/", 1)[-1]
        self.setWindowTitle(f"{name} — {APP_NAME}")
        recovered = sum(1 for r in self.records if r.recovered)
        no_ap = sum(1 for r in self.records if not r.has_ap)
        pages = f"{doc.page_count} page{'s' if doc.page_count != 1 else ''}"
        annots = f"{len(self.records)} annotation{'s' if len(self.records) != 1 else ''}"
        msg = f"{name} · {pages} · {annots}"
        extra = []
        if recovered:
            extra.append(f"{recovered} recovered from the raw /Annots array")
        if no_ap:
            extra.append(f"{no_ap} drawn by GalView (no appearance stream)")
        if extra:
            msg += " · " + ", ".join(extra)
        self._doc_summary = msg
        self.statusBar().showMessage(msg)
        if self.fit_width:
            self._apply_fit_width()
        return True

    # -- review marks -----------------------------------------------------
    def _marks_path(self) -> str:
        return f"{self.path}.galview.json" if self.path else ""

    def _load_marks(self) -> None:
        """Reviewed and dismissed flags live in a sidecar file. The PDF is
        never touched, so a marked-up document stays byte-identical."""
        if not self.remember_marks or not os.path.exists(self._marks_path()):
            return
        try:
            with open(self._marks_path(), "r", encoding="utf-8") as fh:
                data = json.load(fh)
        except Exception:
            return
        by_xref = {r.xref: r.uid for r in self.records}
        self.sidebar.set_marks(
            {by_xref[x] for x in data.get("reviewed", []) if x in by_xref},
            {by_xref[x] for x in data.get("dismissed", []) if x in by_xref})

    def _save_marks(self) -> None:
        if not self.remember_marks or not self.path:
            return
        by_uid = {r.uid: r.xref for r in self.records}
        data = {
            "reviewed": sorted(by_uid[u] for u in self.sidebar.validated if u in by_uid),
            "dismissed": sorted(by_uid[u] for u in self.sidebar.dismissed if u in by_uid),
        }
        try:
            if not data["reviewed"] and not data["dismissed"]:
                if os.path.exists(self._marks_path()):
                    os.remove(self._marks_path())
                return
            with open(self._marks_path(), "w", encoding="utf-8") as fh:
                json.dump(data, fh, indent=1)
        except Exception as exc:
            self.statusBar().showMessage(f"Could not save review marks: {exc}")

    # -- navigation -------------------------------------------------------
    def current_page(self) -> int:
        return max(0, self.view._last_page)

    def jump_page(self, index: int) -> None:
        if not self.doc:
            return
        index = max(0, min(self.doc.page_count - 1, index))
        self.view.goto_page(index)
        self._page_indicator(index)

    def _page_entered(self) -> None:
        try:
            self.jump_page(int(self.page_edit.text()) - 1)
        except ValueError:
            self._page_indicator(self.current_page())

    def _page_indicator(self, index: int) -> None:
        self.view._last_page = index
        self.page_edit.setText(str(index + 1))

    # -- zoom -------------------------------------------------------------
    def set_zoom(self, zoom: float, from_fit: bool = False) -> None:
        if not from_fit:
            self.fit_width = False
        anchor = self._anchor()
        self.view.canvas.set_zoom(zoom)
        self._restore_anchor(anchor)
        if not from_fit:
            self._sync_zoom_box(zoom)

    def _sync_zoom_box(self, zoom: float) -> None:
        for i, z in enumerate(ZOOMS):
            if abs(z - zoom) < 1e-6:
                self.zoom_box.setCurrentIndex(i)
                return
        self.zoom_box.setCurrentIndex(-1)
        self.zoom_box.setEditText(f"{int(zoom * 100)}%")

    def step_zoom(self, direction: int) -> None:
        cur = self.view.canvas.zoom
        if direction > 0:
            nxt = next((z for z in ZOOMS if z > cur + 1e-6), min(8.0, cur * 1.25))
        else:
            nxt = next((z for z in reversed(ZOOMS) if z < cur - 1e-6), max(0.1, cur / 1.25))
        self.set_zoom(nxt)

    def _zoom_chosen(self, index: int) -> None:
        data = self.zoom_box.itemData(index)
        if data == "fit":
            self.fit_width = True
            self._apply_fit_width()
        elif data:
            self.set_zoom(float(data))

    def _apply_fit_width(self) -> None:
        if not self.doc:
            return
        widest = max((self.view.canvas._boxes[i].width
                      for i in range(len(self.view.canvas._boxes))), default=1)
        avail = self.view.viewport().width() - 2 * MARGIN - 4
        if widest > 0 and avail > 40:
            self.set_zoom(avail / widest, from_fit=True)

    def _anchor(self):
        page = self.current_page()
        pr = self.view.canvas.page_rect(page)
        if pr.isNull():
            return None
        off = self.view.verticalScrollBar().value() - pr.top()
        return page, off / max(1, pr.height())

    def _restore_anchor(self, anchor) -> None:
        if not anchor:
            return
        page, frac = anchor
        pr = self.view.canvas.page_rect(page)
        if pr.isNull():
            return
        self.view.verticalScrollBar().setValue(int(pr.top() + frac * pr.height()))

    def resizeEvent(self, event) -> None:
        super().resizeEvent(event)
        if self.fit_width:
            QTimer.singleShot(0, self._apply_fit_width)

    def _toggle_outlines(self, on: bool) -> None:
        self.view.canvas.show_outlines = on
        self.view.canvas.update()

    # -- annotation focus -------------------------------------------------
    def focus_annotation(self, uid: int) -> None:
        rec = next((r for r in self.records if r.uid == uid), None)
        if rec is None:
            return
        self.view.canvas.select(uid)
        self.sidebar.select(uid)
        if rec.rect is not None and not rec.rect.is_empty:
            self.view.reveal(rec.page, rec.rect)
        else:
            self.view.goto_page(rec.page)
        self._page_indicator(rec.page)
        who = rec.author or "unknown author"
        stack = sum(1 for other in self.records
                    if other.page == rec.page and other.rect is not None
                    and rec.rect is not None and other.rect.intersects(rec.rect))
        note = f" · {stack} annotations overlap here" if stack > 1 else ""
        self.statusBar().showMessage(
            f"{rec.label} by {who} on page {rec.page + 1}{note}")

    def clear_annotation(self) -> None:
        """Clicking bare page area drops the selection and its rectangle."""
        self.view.canvas.select(None)
        self.sidebar.select(None, scroll=False)
        self.statusBar().showMessage(self._doc_summary)

    # -- search -----------------------------------------------------------
    def open_search(self) -> None:
        self.search.show()
        self.search.field.setFocus()
        self.search.field.selectAll()

    def close_search(self) -> None:
        if not self.search.isVisible():
            return
        self.search.hide()
        self.hits = []
        self.hit_index = -1
        self.view.canvas.hits = []
        self.view.canvas.current_hit = -1
        self.view.canvas.update()
        self.sidebar.apply_filter("")

    def _search_changed(self, term: str) -> None:
        self.hits = []
        self.hit_index = -1
        term = term.strip()
        if self.doc and len(term) >= 1:
            for pno in range(self.doc.page_count):
                try:
                    for rect in self.doc[pno].search_for(term):
                        self.hits.append((pno, fitz.Rect(rect)))
                except Exception:
                    continue
        self.view.canvas.hits = self.hits
        self.view.canvas.current_hit = -1
        self.view.canvas.update()
        self.sidebar.apply_filter(term)
        annots = self.sidebar.matches(term)
        if not term:
            self.search.status.setText("")
        else:
            self.search.status.setText(
                f"{len(self.hits)} in text · {annots} in annotations")

    def step_hit(self, direction: int) -> None:
        if not self.hits:
            if self.search.field.text().strip():
                self.search.status.setText("No match in the page text")
            return
        self.hit_index = (self.hit_index + direction) % len(self.hits)
        page, rect = self.hits[self.hit_index]
        self.view.canvas.current_hit = self.hit_index
        self.view.canvas.update()
        self.view.reveal(page, rect)
        self._page_indicator(page)
        annots = self.sidebar.matches(self.search.field.text())
        self.search.status.setText(
            f"{self.hit_index + 1} of {len(self.hits)} in text · {annots} in annotations")


# ---------------------------------------------------------------------------

def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="galview", description="Read-only PDF viewer focused on annotations.")
    parser.add_argument("pdf", nargs="?", help="PDF file to open")
    parser.add_argument("--page", type=int, default=1, help="page to open at (1-based)")
    parser.add_argument("--no-marks", action="store_true",
                        help="do not read or write the .galview.json sidecar "
                             "that remembers reviewed and dismissed entries")
    args = parser.parse_args(argv)

    app = QApplication(sys.argv[:1])
    app.setApplicationName(APP_NAME)
    win = MainWindow()
    win.remember_marks = not args.no_marks
    win.show()
    if args.pdf:
        if win.load(args.pdf) and args.page > 1:
            QTimer.singleShot(0, lambda: win.jump_page(args.page - 1))
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())

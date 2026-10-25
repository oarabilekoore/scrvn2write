#!/usr/bin/env python3
"""
Converter between Scrivano (.scrvn), Stylus Labs Write (.svgz) and Xournal++ (.xopp)

Usage:
  python3 scrvn2write.py to-write  "Lab 5.scrvn" "Lab 5.svgz"
  python3 scrvn2write.py to-scrvn  "Lab 5.svgz"  "Lab 5_back.scrvn"
  python3 scrvn2write.py to-xopp   "Lab 5.scrvn" "Lab 5.xopp"      (input may also be .svgz)

Options:
  --write-dpi N            pixels-per-inch of the Write document (default 150; A4 = 1240 x 1755 px)
  --xopp-ruling MODE       layer  (default) exact ruling/margin drawn on a separate "Ruling" layer
                           native           use Xournal++'s built-in lined/graph/dotted background

Optional packages:
  zstandard   needed to read .scrvn files on Python < 3.14 (Scrivano compresses with Zstandard)
  Pillow      JPEG->PNG conversion of pasted images, rotated images, real page thumbnails

Coordinate systems (all verified against Lab_5.scrvn / Lab_5.pdf):
  Scrivano   1 unit = 1/160 inch = 0.45 pt.  Stroke points, stroke widths and image rectangles
             all use this one unit (A4 page = 1322.83 x 1870.87 units).
  Write      1 px   = 1/150 inch (A4 = 1240 x 1755 px).      => Scrivano -> Write scale = 150/160
  Xournal++  1 pt   = 1/72 inch.                              => Scrivano -> xopp  scale = 0.45
"""

import argparse
import base64
import gzip
import hashlib
import io
import math
import os
import re
import struct
import sys
import time
import uuid
import xml.etree.ElementTree as ET
import zipfile
import zlib
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

try:
    from PIL import Image, ImageDraw, ImageOps
    HAVE_PIL = True
except ImportError:  # Pillow is optional
    HAVE_PIL = False

# =====================================================================
# CONSTANTS
# =====================================================================
U_PER_INCH = 160.0                  # Scrivano units per inch
MM_PER_INCH = 25.4
U_PER_MM = U_PER_INCH / MM_PER_INCH
PT_PER_U = 72.0 / U_PER_INCH        # 0.45
WRITE_DPI = 150.0                   # Write px per inch (A4 = 1240 x 1755)

# Where Scrivano draws the first ruled line, measured from the top of the page (page 3 of the
# sample: 16.89 pt = 37.5 units). Spacing/margin come from documentinfo.
RULE_FIRST_OFFSET_U = 37.5

# documentinfo paper types. Only 2 (= ruled) is confirmed by a real file; the others are inferred.
PAPER_BLANK, PAPER_GRID, PAPER_RULED, PAPER_DOTTED = 0, 1, 2, 3

PAGE_PRESETS = {
    "A3": (297.0, 420.0), "A4": (210.0, 297.0), "A5": (148.0, 210.0), "A6": (105.0, 148.0),
    "B5": (176.0, 250.0), "Letter": (215.9, 279.4), "Legal": (215.9, 355.6),
}

# Fallback 16x16 white PNG used when Pillow is unavailable
THUMB_PNG = base64.b64decode(
    "iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAIAAACQkWg2AAAAFUlEQVR4nGP8//8/AzWAiSTVg1U1"
    "AA5fAwH27n96AAAAAElFTkSuQmCC"
)


# =====================================================================
# DATA STRUCTURES
# =====================================================================
@dataclass
class PaperStyle:
    paper_type: int = PAPER_RULED
    x_spacing_mm: float = 10.0
    y_spacing_mm: float = 10.0
    rule_color: str = "#e0e0e0"
    paper_color: str = "#ffffff"
    show_margin: int = 1
    margin_mm: float = 15.0
    margin_color: str = "#db544b"
    size_name: str = "A4"
    width_mm: float = 210.0
    height_mm: float = 297.0


@dataclass
class Stroke:
    color: str = "#ff000000"        # #AARRGGBB
    width: float = 1.97755          # Scrivano units
    points: List[Tuple[float, float]] = field(default_factory=list)   # Scrivano units
    timestamp: int = 0
    stroke_id: int = 0


@dataclass
class ImageItem:
    name: str                       # key in ScrvnDoc.images, e.g. "{uuid}.png"
    x: float = 0.0                  # Scrivano units
    y: float = 0.0
    w: float = 0.0
    h: float = 0.0
    timestamp: int = 0
    extra_f4: float = 360.0         # unknown float stored by Scrivano (360.0 in every sample)


@dataclass
class ScrvnPage:
    uuid_str: str
    strokes: List[Stroke] = field(default_factory=list)
    images: List[ImageItem] = field(default_factory=list)


@dataclass
class ScrvnDoc:
    title: str = "Note"
    style: PaperStyle = field(default_factory=PaperStyle)
    pages: List[ScrvnPage] = field(default_factory=list)
    images: Dict[str, bytes] = field(default_factory=dict)       # "{uuid}.png" -> PNG bytes
    warnings: List[str] = field(default_factory=list)


# =====================================================================
# PROTOBUF WIRE HELPERS
# =====================================================================
def encode_varint(val: int) -> bytes:
    if val < 0:
        val += 1 << 64
    out = bytearray()
    while val > 0x7F:
        out.append((val & 0x7F) | 0x80)
        val >>= 7
    out.append(val & 0x7F)
    return bytes(out)


def decode_varint(data: bytes, offset: int) -> Tuple[int, int]:
    val = shift = 0
    while offset < len(data):
        b = data[offset]
        offset += 1
        val |= (b & 0x7F) << shift
        if not b & 0x80:
            return val, offset
        shift += 7
    raise ValueError("Truncated varint")


def enc_tag(fnum: int, wtype: int) -> bytes:
    return encode_varint((fnum << 3) | wtype)


def enc_varint(fnum: int, val: int) -> bytes:
    return enc_tag(fnum, 0) + encode_varint(val)


def enc_float(fnum: int, val: float) -> bytes:
    return enc_tag(fnum, 5) + struct.pack("<f", val)


def enc_bytes(fnum: int, val: bytes) -> bytes:
    return enc_tag(fnum, 2) + encode_varint(len(val)) + val


def enc_string(fnum: int, val: str) -> bytes:
    return enc_bytes(fnum, val.encode("utf-8"))


def iter_fields(data: bytes):
    """Yields (field_number, wire_type, value)."""
    off, n = 0, len(data)
    while off < n:
        tag, off = decode_varint(data, off)
        fnum, wtype = tag >> 3, tag & 7
        if wtype == 0:
            val, off = decode_varint(data, off)
        elif wtype == 1:
            val = data[off:off + 8]
            off += 8
        elif wtype == 2:
            ln, off = decode_varint(data, off)
            val = data[off:off + ln]
            off += ln
        elif wtype == 5:
            val = data[off:off + 4]
            off += 4
        else:
            raise ValueError(f"Unsupported wire type {wtype}")
        yield fnum, wtype, val


def f32(b: bytes) -> float:
    return struct.unpack("<f", b)[0]


# =====================================================================
# COLOUR / GEOMETRY HELPERS
# =====================================================================
_NAMED = {
    "black": (0, 0, 0), "white": (255, 255, 255), "red": (255, 0, 0), "green": (0, 128, 0),
    "blue": (0, 0, 255), "yellow": (255, 255, 0), "gray": (128, 128, 128), "grey": (128, 128, 128),
    "orange": (255, 165, 0), "purple": (128, 0, 128), "cyan": (0, 255, 255), "magenta": (255, 0, 255),
}


def parse_color(s: Optional[str], default=(0, 0, 0, 255)):
    """Returns (r, g, b, a) or None for 'none'. 8-digit hex is AARRGGBB (Scrivano and Write dialect)."""
    if s is None:
        return default
    s = s.strip().lower()
    if not s or s in ("currentcolor", "inherit"):
        return default
    if s == "none":
        return None
    if s in _NAMED:
        return _NAMED[s] + (255,)
    m = re.fullmatch(r"rgb\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)", s)
    if m:
        return int(m.group(1)), int(m.group(2)), int(m.group(3)), 255
    if s.startswith("#"):
        h = s[1:]
        try:
            if len(h) == 3:
                return int(h[0] * 2, 16), int(h[1] * 2, 16), int(h[2] * 2, 16), 255
            if len(h) == 6:
                return int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16), 255
            if len(h) == 8:
                return int(h[2:4], 16), int(h[4:6], 16), int(h[6:8], 16), int(h[0:2], 16)
        except ValueError:
            pass
    return default


def c_rgb(c) -> str:        # '#RRGGBB'
    return "#%02X%02X%02X" % c[:3]


def c_argb(c) -> str:       # Scrivano '#aarrggbb'
    return "#%02x%02x%02x%02x" % (c[3], c[0], c[1], c[2])


def c_write(c) -> str:      # Write '#AARRGGBB'
    return "#%02X%02X%02X%02X" % (c[3], c[0], c[1], c[2])


def c_xopp(c) -> str:       # Xournal++ '#rrggbbaa'
    return "#%02x%02x%02x%02x" % c


def blend_on(c, bg):
    """Alpha-blend colour c over opaque bg, returns opaque (r,g,b,255)."""
    a = c[3] / 255.0
    return tuple(int(round(c[i] * a + bg[i] * (1 - a))) for i in range(3)) + (255,)


def snap_mm(v: float) -> float:
    """Snap a measurement to 0.5 mm when within pixel-rounding error, else keep 0.1 mm."""
    r = round(v * 2) / 2
    return r if abs(r - v) <= 0.15 else round(v, 1)


def page_units(style: PaperStyle) -> Tuple[float, float]:
    return style.width_mm * U_PER_MM, style.height_mm * U_PER_MM


def match_page_size(w_mm: float, h_mm: float) -> Tuple[str, float, float]:
    for name, (pw, ph) in PAGE_PRESETS.items():
        if abs(w_mm - pw) < 2 and abs(h_mm - ph) < 2:
            return name, pw, ph
        if abs(w_mm - ph) < 2 and abs(h_mm - pw) < 2:
            return name, ph, pw
    return "Custom", round(w_mm, 1), round(h_mm, 1)


def write_page_px(style: PaperStyle, dpi: float) -> Tuple[int, int]:
    if dpi == 150.0 and abs(style.width_mm - 210) < 0.5 and abs(style.height_mm - 297) < 0.5:
        return 1240, 1755
    return (int(round(style.width_mm / MM_PER_INCH * dpi)),
            int(round(style.height_mm / MM_PER_INCH * dpi)))


def ruling_geometry(style: PaperStyle, page_w_u: float, page_h_u: float) -> dict:
    """Ruling as Scrivano draws it, in Scrivano units: horizontal y's, vertical x's, margin x, dot grid."""
    ysp = style.y_spacing_mm * U_PER_MM
    xsp = style.x_spacing_mm * U_PER_MM
    hs: List[float] = []
    vs: List[float] = []
    if style.paper_type in (PAPER_RULED, PAPER_GRID, PAPER_DOTTED) and ysp > 1:
        y = RULE_FIRST_OFFSET_U
        while y < page_h_u - 0.5:
            hs.append(y)
            y += ysp
    if style.paper_type in (PAPER_GRID, PAPER_DOTTED) and xsp > 1:
        x = xsp
        while x < page_w_u - 0.5:
            vs.append(x)
            x += xsp
    margin = style.margin_mm * U_PER_MM if style.show_margin and style.margin_mm > 0 else None
    return {"h": hs if style.paper_type != PAPER_DOTTED else [],
            "v": vs if style.paper_type == PAPER_GRID else [],
            "dots": [(x, y) for y in hs for x in vs] if style.paper_type == PAPER_DOTTED else [],
            "margin": margin, "ysp": ysp, "xsp": xsp, "dot_rows": hs, "dot_cols": vs}


def get_png_dimensions(png: bytes) -> Tuple[int, int]:
    if len(png) >= 24 and png[:8] == b"\x89PNG\r\n\x1a\n":
        return struct.unpack(">II", png[16:24])
    return 0, 0


# =====================================================================
# ZIP READING (Scrivano uses Zstandard = method 93, unsupported by zipfile before Python 3.14)
# =====================================================================
def _zstd_decompress(raw: bytes, size: int) -> bytes:
    try:
        from compression import zstd  # Python 3.14+
        return zstd.decompress(raw)
    except ImportError:
        pass
    try:
        import zstandard
        return zstandard.ZstdDecompressor().decompress(raw, max_output_size=max(size, 1))
    except ImportError:
        raise SystemExit("This .scrvn uses Zstandard compression.\n"
                         "Install the decoder with:  pip install zstandard   (or use Python 3.14+)")


def _read_zip_manual(path: str) -> Dict[str, bytes]:
    data = open(path, "rb").read()
    eocd = data.rfind(b"PK\x05\x06")
    if eocd < 0:
        raise ValueError("Not a zip file")
    n, _cdsize, cdoff = struct.unpack("<HII", data[eocd + 10:eocd + 20])
    out: Dict[str, bytes] = {}
    p = cdoff
    for _ in range(n):
        (_, _, _, method, _, _, _crc, csz, usz, fl, el, cl, _, _, _, lho) = \
            struct.unpack("<HHHHHHIIIHHHHHII", data[p + 4:p + 46])
        name = data[p + 46:p + 46 + fl].decode("utf-8")
        p += 46 + fl + el + cl
        lfl, lel = struct.unpack("<HH", data[lho + 26:lho + 30])
        start = lho + 30 + lfl + lel
        raw = data[start:start + csz]
        if name.endswith("/"):
            continue
        if method == 0:
            out[name] = raw
        elif method == 8:
            out[name] = zlib.decompress(raw, -15)
        elif method == 93:
            out[name] = _zstd_decompress(raw, usz)
        else:
            raise ValueError(f"Unsupported zip compression method {method} for {name}")
    return out


def read_zip_entries(path: str) -> Dict[str, bytes]:
    try:
        with zipfile.ZipFile(path) as z:
            return {n: z.read(n) for n in z.namelist() if not n.endswith("/")}
    except NotImplementedError:
        return _read_zip_manual(path)


# =====================================================================
# SCRIVANO (.scrvn) READER
# =====================================================================
def parse_style_msg(data: bytes) -> Tuple[str, float]:
    color, width = "#ff000000", 1.97755
    for fn, wt, v in iter_fields(data):
        if fn == 1 and wt == 2:
            color = v.decode("utf-8", "ignore")
        elif fn == 2 and wt == 5:
            width = f32(v)
    return color, width


def parse_point(data: bytes) -> Tuple[float, float]:
    x = y = 0.0
    for fn, wt, v in iter_fields(data):
        if fn == 1 and wt == 5:
            x = f32(v)
        elif fn == 2 and wt == 5:
            y = f32(v)
    return x, y


def parse_stroke_msg(data: bytes) -> Stroke:
    st = Stroke()
    for fn, wt, v in iter_fields(data):
        if fn == 1 and wt == 2:
            st.points.append(parse_point(v))
        elif fn == 2 and wt == 2:
            st.color, st.width = parse_style_msg(v)
        elif fn == 3 and wt == 0:
            st.timestamp = v
        elif fn == 4 and wt == 0:
            st.stroke_id = v
    return st


def parse_line_msg(data: bytes) -> Stroke:
    """Page field 3: straight-line stroke (style, timestamp, {points})."""
    st = Stroke()
    for fn, wt, v in iter_fields(data):
        if fn == 1 and wt == 2:
            st.color, st.width = parse_style_msg(v)
        elif fn == 2 and wt == 0:
            st.timestamp = v
        elif fn == 4 and wt == 2:
            for sf, sw, sv in iter_fields(v):
                if sf == 1 and sw == 2:
                    st.points.append(parse_point(sv))
    return st


def parse_image_msg(data: bytes, known: set) -> Optional[ImageItem]:
    """Page field 2: {1: "{uuid}", 2: {x, y, w, h}, 3: timestamp, 4: float}."""
    item = None
    for fn, wt, v in iter_fields(data):
        if fn == 1 and wt == 2:
            u = v.decode("utf-8", "ignore").replace(".png", "")
            if u in known:
                item = ImageItem(name=u + ".png")
    if item is None:
        return None
    for fn, wt, v in iter_fields(data):
        if fn == 2 and wt == 2:
            vals = {sf: f32(sv) for sf, sw, sv in iter_fields(v) if sw == 5}
            item.x, item.y = vals.get(1, 0.0), vals.get(2, 0.0)
            item.w, item.h = vals.get(3, 0.0), vals.get(4, 0.0)
        elif fn == 3 and wt == 0:
            item.timestamp = v
        elif fn == 4 and wt == 5:
            item.extra_f4 = f32(v)
    return item


def parse_documentinfo(raw: bytes) -> Tuple[str, PaperStyle]:
    title, st = "Note", PaperStyle()
    for fn, wt, v in iter_fields(raw):
        if fn == 1 and wt == 2:
            title = v.decode("utf-8", "ignore")
        elif fn == 7 and wt == 2:
            for sf, sw, sv in iter_fields(v):
                if sf == 1000 and sw == 2:
                    for bf, bw, bv in iter_fields(sv):
                        if bf == 1 and bw == 0:
                            st.paper_type = bv
                        elif bf == 2 and bw == 5:
                            st.x_spacing_mm = f32(bv)
                        elif bf == 3 and bw == 5:
                            st.y_spacing_mm = f32(bv)
                        elif bf == 4 and bw == 2:
                            st.rule_color = bv.decode("utf-8", "ignore")
                        elif bf == 5 and bw == 2:
                            st.paper_color = bv.decode("utf-8", "ignore")
                        elif bf == 6 and bw == 0:
                            st.show_margin = bv
                        elif bf == 7 and bw == 5:
                            st.margin_mm = f32(bv)
                        elif bf == 8 and bw == 2:
                            if bv[:1] == b"#":
                                st.margin_color = bv.decode("utf-8", "ignore")
                            else:
                                for pf, pw, pv in iter_fields(bv):
                                    if pf == 1 and pw == 2:
                                        st.size_name = pv.decode("utf-8", "ignore")
                                    elif pf == 2 and pw == 5:
                                        st.width_mm = f32(pv)
                                    elif pf == 3 and pw == 5:
                                        st.height_mm = f32(pv)
    return title, st


def read_scrvn(path: str) -> ScrvnDoc:
    doc = ScrvnDoc()
    files = read_zip_entries(path)
    known = set()
    for name, data in files.items():
        if name.startswith("images/") and name.lower().endswith(".png"):
            base = os.path.basename(name)
            doc.images[base] = data
            known.add(base[:-4])
    if "documentinfo" in files:
        doc.title, doc.style = parse_documentinfo(files["documentinfo"])

    entries: List[Tuple[int, str]] = []
    for fn, wt, v in iter_fields(files.get("pages/pageinfolist", b"")):
        if wt != 2:
            continue
        idx, uid = len(entries), None
        for sf, sw, sv in iter_fields(v):
            if sf == 1 and sw == 0:
                idx = sv
            elif sf == 2 and sw == 2:
                uid = sv.decode("utf-8")
        if uid:
            entries.append((idx, uid))
    entries.sort(key=lambda e: e[0])

    unknown = set()
    for _, uid in entries:
        raw = files.get(f"pages/{uid}")
        if raw is None:
            doc.warnings.append(f"page {uid} listed but missing from archive")
            continue
        page = ScrvnPage(uuid_str=uid)
        for fn, wt, v in iter_fields(raw):
            if fn == 1 and wt == 2:
                st = parse_stroke_msg(v)
                if st.points:
                    page.strokes.append(st)
            elif fn == 2 and wt == 2:
                img = parse_image_msg(v, known)
                if img:
                    page.images.append(img)
                else:
                    doc.warnings.append("image record references a missing image file")
            elif fn == 3 and wt == 2:
                st = parse_line_msg(v)
                if st.points:
                    page.strokes.append(st)
            elif fn not in (1000, 1002):
                unknown.add(fn)
        doc.pages.append(page)
    if unknown:
        doc.warnings.append(f"ignored unknown page fields: {sorted(unknown)}")
    return doc


# =====================================================================
# TRANSFORMS + SVG PATH PARSING (for reading Write documents)
# =====================================================================
Matrix = Tuple[float, float, float, float, float, float]
IDENT: Matrix = (1, 0, 0, 1, 0, 0)


def mat_mul(m: Matrix, n: Matrix) -> Matrix:
    """m * n (n is applied first)."""
    return (m[0] * n[0] + m[2] * n[1], m[1] * n[0] + m[3] * n[1],
            m[0] * n[2] + m[2] * n[3], m[1] * n[2] + m[3] * n[3],
            m[0] * n[4] + m[2] * n[5] + m[4], m[1] * n[4] + m[3] * n[5] + m[5])


def mat_apply(m: Matrix, x: float, y: float) -> Tuple[float, float]:
    return m[0] * x + m[2] * y + m[4], m[1] * x + m[3] * y + m[5]


def mat_scale(m: Matrix) -> float:
    return math.sqrt(abs(m[0] * m[3] - m[1] * m[2]))


def parse_transform(s: Optional[str]) -> Matrix:
    m = IDENT
    if not s:
        return m
    for name, args in re.findall(r"(\w+)\s*\(([^)]*)\)", s):
        a = [float(v) for v in re.findall(r"[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?", args)]
        t = IDENT
        if name == "matrix" and len(a) == 6:
            t = tuple(a)
        elif name == "translate" and a:
            t = (1, 0, 0, 1, a[0], a[1] if len(a) > 1 else 0)
        elif name == "scale" and a:
            t = (a[0], 0, 0, a[1] if len(a) > 1 else a[0], 0, 0)
        elif name == "rotate" and a:
            r = math.radians(a[0])
            c, s_ = math.cos(r), math.sin(r)
            t = (c, s_, -s_, c, 0, 0)
            if len(a) == 3:
                t = mat_mul(mat_mul((1, 0, 0, 1, a[1], a[2]), t), (1, 0, 0, 1, -a[1], -a[2]))
        elif name == "skewx" and a:
            t = (1, 0, math.tan(math.radians(a[0])), 1, 0, 0)
        elif name == "skewy" and a:
            t = (1, math.tan(math.radians(a[0])), 0, 1, 0, 0)
        m = mat_mul(m, t)
    return m


_PATH_TOK = re.compile(r"([MmLlHhVvCcSsQqTtAaZz])|([-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?)")
_NARGS = {"M": 2, "L": 2, "H": 1, "V": 1, "C": 6, "S": 4, "Q": 4, "T": 2, "A": 7}


def parse_path(d: str) -> List[List[Tuple[float, float]]]:
    """Flattens an SVG path into a list of polylines (curves sampled, arcs approximated by chords)."""
    toks = [(m.group(1), m.group(2)) for m in _PATH_TOK.finditer(d)]
    subs: List[List[Tuple[float, float]]] = []
    cur: List[Tuple[float, float]] = []
    x = y = sx = sy = 0.0
    cmd = None
    lastc = None
    i = 0

    def cubic(p0, p1, p2, p3, n=10):
        for k in range(1, n + 1):
            t = k / n
            u = 1 - t
            cur.append((u**3 * p0[0] + 3 * u * u * t * p1[0] + 3 * u * t * t * p2[0] + t**3 * p3[0],
                        u**3 * p0[1] + 3 * u * u * t * p1[1] + 3 * u * t * t * p2[1] + t**3 * p3[1]))

    while i < len(toks):
        c, nv = toks[i]
        if c:
            cmd = c
            i += 1
            if cmd in "Zz":
                if cur:
                    subs.append(cur)
                cur = []
                x, y = sx, sy
                lastc = None
                continue
        elif cmd is None or cmd in "Zz":
            break
        elif cmd == "M":
            cmd = "L"
        elif cmd == "m":
            cmd = "l"
        up, rel = cmd.upper(), cmd.islower()
        k = _NARGS[up]
        if i + k > len(toks) or any(toks[i + j][1] is None for j in range(k)):
            break
        v = [float(toks[i + j][1]) for j in range(k)]
        i += k
        ox, oy = (x, y) if rel else (0.0, 0.0)
        if up == "M":
            if cur:
                subs.append(cur)
            x, y = ox + v[0], oy + v[1]
            sx, sy = x, y
            cur = [(x, y)]
            lastc = None
        else:
            if not cur:
                cur = [(x, y)]
            if up == "L":
                x, y = ox + v[0], oy + v[1]
                cur.append((x, y))
                lastc = None
            elif up == "H":
                x = (x if rel else 0.0) + v[0]
                cur.append((x, y))
                lastc = None
            elif up == "V":
                y = (y if rel else 0.0) + v[0]
                cur.append((x, y))
                lastc = None
            elif up == "C":
                p1, p2, p3 = (ox + v[0], oy + v[1]), (ox + v[2], oy + v[3]), (ox + v[4], oy + v[5])
                cubic((x, y), p1, p2, p3)
                x, y = p3
                lastc = p2
            elif up == "S":
                p1 = (2 * x - lastc[0], 2 * y - lastc[1]) if lastc else (x, y)
                p2, p3 = (ox + v[0], oy + v[1]), (ox + v[2], oy + v[3])
                cubic((x, y), p1, p2, p3)
                x, y = p3
                lastc = p2
            elif up in ("Q", "T"):
                if up == "Q":
                    q1, q2 = (ox + v[0], oy + v[1]), (ox + v[2], oy + v[3])
                else:
                    q1 = (2 * x - lastc[0], 2 * y - lastc[1]) if lastc else (x, y)
                    q2 = (ox + v[0], oy + v[1])
                p0 = (x, y)
                c1 = (p0[0] + 2 / 3 * (q1[0] - p0[0]), p0[1] + 2 / 3 * (q1[1] - p0[1]))
                c2 = (q2[0] + 2 / 3 * (q1[0] - q2[0]), q2[1] + 2 / 3 * (q1[1] - q2[1]))
                cubic(p0, c1, c2, q2, 8)
                x, y = q2
                lastc = q1
            elif up == "A":
                x, y = ox + v[5], oy + v[6]
                cur.append((x, y))
                lastc = None
    if cur:
        subs.append(cur)
    return subs


# =====================================================================
# WRITE (.svgz) EXPORTER
# =====================================================================
def make_ribbon(points: List[Tuple[float, float]], width: float) -> List[Tuple[float, float]]:
    """Closed outline polygon of a constant-width stroke: left side forward, right side back.
    Vertex i pairs with vertex 2n-1-i, which is what read_write_svgz uses to recover the centreline."""
    hw = max(width / 2.0, 0.3)
    p = [points[0]]
    for q in points[1:]:
        if math.hypot(q[0] - p[-1][0], q[1] - p[-1][1]) >= 0.05:
            p.append(q)
    n = len(p)
    if n == 1:
        x, y = p[0]
        return [(x + hw * math.cos(k * math.pi / 4), y + hw * math.sin(k * math.pi / 4)) for k in range(8)]
    normals = []
    for i in range(n - 1):
        dx, dy = p[i + 1][0] - p[i][0], p[i + 1][1] - p[i][1]
        ln = math.hypot(dx, dy)
        normals.append((-dy / ln, dx / ln))
    left, right = [], []
    for i in range(n):
        if i == 0:
            nx, ny = normals[0]
            s = 1.0
        elif i == n - 1:
            nx, ny = normals[-1]
            s = 1.0
        else:
            mx, my = normals[i - 1][0] + normals[i][0], normals[i - 1][1] + normals[i][1]
            ml = math.hypot(mx, my)
            if ml < 1e-6:                       # 180-degree reversal
                nx, ny = normals[i]
                s = 1.0
            else:
                nx, ny = mx / ml, my / ml
                s = min(2.0 / ml, 2.5)          # miter, clamped
        left.append((p[i][0] + nx * hw * s, p[i][1] + ny * hw * s))
        right.append((p[i][0] - nx * hw * s, p[i][1] - ny * hw * s))
    return left + right[::-1]


def polygon_to_d(poly: List[Tuple[float, float]]) -> str:
    x0, y0 = poly[0]
    cx, cy = round(x0, 3), round(y0, 3)
    parts = []
    for px, py in poly[1:]:
        dx, dy = round(px - cx, 3), round(py - cy, 3)
        parts.append(f"{dx:g} {dy:g}")
        cx, cy = round(cx + dx, 3), round(cy + dy, 3)
    return f"M{round(x0, 3):g} {round(y0, 3):g} l" + " ".join(parts)


def _write_ruling_markup(style: PaperStyle, pw: int, ph: int, dpi: float, page_idx: int):
    """Returns (write-content attrs dict, list of svg lines for g.ruleline children)."""
    s = dpi / U_PER_INCH
    uw, uh = page_units(style)
    geo = ruling_geometry(style, uw, uh)
    paper = parse_color(style.paper_color, (255, 255, 255, 255))
    rule = parse_color(style.rule_color, (224, 224, 224, 255))
    mcol = parse_color(style.margin_color, (219, 84, 75, 255))
    paper_hex, rule_hex, mcol_hex = c_rgb(paper), c_rgb(rule), c_rgb(mcol)
    margin_px = int(round(style.margin_mm / MM_PER_INCH * dpi)) if geo["margin"] else 0
    dotted = style.paper_type == PAPER_DOTTED
    yruling = 0 if dotted else (int(round(style.y_spacing_mm / MM_PER_INCH * dpi))
                                if style.paper_type in (PAPER_RULED, PAPER_GRID) else 0)
    xruling = int(round(style.x_spacing_mm / MM_PER_INCH * dpi)) if style.paper_type == PAPER_GRID else 0
    attrs = {"width": pw, "height": ph, "xruling": xruling, "yruling": yruling,
             "marginLeft": margin_px, "papercolor": paper_hex, "rulecolor": c_write(rule[:3] + (255,))}
    out = [f'      <rect class="pagerect" fill="{paper_hex}" stroke="none" x="0" y="0" width="{pw}" height="{ph}" />']
    first = True
    for y in geo["h"]:
        cls = ' class="yrule_1"' if first else ""
        first = False
        out.append(f'      <path{cls} d="M0 {int(round(y * s))} l{pw} 0" />')
    for x in geo["v"]:
        out.append(f'      <path d="M{int(round(x * s))} 0 l0 {ph}" />')
    if dotted and geo["dot_rows"] and geo["dot_cols"]:
        tw, th = geo["xsp"] * s, geo["ysp"] * s
        x0, y0 = geo["dot_cols"][0] * s, geo["dot_rows"][0] * s
        pid = f"dots_{page_idx + 1:03d}"
        out.append(f'      <pattern id="{pid}" x="{x0 - tw / 2:.3f}" y="{y0 - th / 2:.3f}" '
                   f'width="{tw:.3f}" height="{th:.3f}" patternUnits="userSpaceOnUse">'
                   f'<circle cx="{tw / 2:.3f}" cy="{th / 2:.3f}" r="1.2" fill="{rule_hex}" stroke="none" /></pattern>')
        out.append(f'      <rect fill="url(#{pid})" stroke="none" x="0" y="0" width="{pw}" height="{ph}" />')
    if margin_px > 0:
        out.append(f'      <path class="leftmargin" stroke="{mcol_hex}" d="M{margin_px} 0 l0 {ph}" />')
    return attrs, out, rule_hex


def export_to_write_svgz(doc: ScrvnDoc, out_path: str, dpi: float = WRITE_DPI):
    st = doc.style
    s = dpi / U_PER_INCH                          # Scrivano units -> Write px
    pw, ph = write_page_px(st, dpi)
    x_off, gap = 10, 10

    lines = ['<svg id="write-document" xmlns="http://www.w3.org/2000/svg" '
             'xmlns:xlink="http://www.w3.org/1999/xlink">',
             '<rect id="write-doc-background" width="100%" height="100%" fill="#808080"/>']
    use_tags = []
    y_cursor = 10
    for idx, page in enumerate(doc.pages):
        pid = f"page_{idx + 1:03d}"
        use_tags.append(f'  <use id="use_{pid}" href="#{pid}" x="{x_off}" y="{y_cursor}" '
                        f'width="{pw}" height="{ph}"/>')
        attrs, ruling, rule_hex = _write_ruling_markup(st, pw, ph, dpi, idx)
        lines.append(f'<svg id="{pid}" class="write-page" color-interpolation="linearRGB" '
                     f'x="{x_off}" y="{y_cursor}" width="{pw}px" height="{ph}px" '
                     f'xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink">')
        lines.append('  <g class="write-content write-v3" ' +
                     " ".join(f'{k}="{v}"' for k, v in attrs.items()) + '>')
        lines.append(f'    <g class="ruleline write-std-ruling write-scale-down" fill="none" '
                     f'stroke="{rule_hex}" stroke-width="1" shape-rendering="crispEdges" '
                     f'vector-effect="non-scaling-stroke">')
        lines.extend(ruling)
        lines.append('    </g>')

        # Images: after g.ruleline, so Write treats them as editable page content
        for n_img, im in enumerate(page.images, 1):
            data = doc.images.get(im.name)
            if data is None:
                continue
            ix, iy, iw, ih = im.x * s, im.y * s, im.w * s, im.h * s
            ts = hex(im.timestamp if im.timestamp else int(time.time() * 1000))
            b64 = base64.b64encode(data).decode("ascii")
            lines.append(f'    <image id="img_{idx + 1:03d}_{n_img}" '
                         f'x="{ix:.2f}" y="{iy:.2f}" width="{iw:.2f}" height="{ih:.2f}" '
                         f'preserveAspectRatio="none" __comx="{ix + iw / 2:.3f}" __comy="{iy + ih / 2:.3f}" '
                         f'__timestamp="{ts}" xlink:href="data:image/png;base64,{b64}" />')

        # Strokes
        for sk in page.strokes:
            if not sk.points:
                continue
            col = parse_color(sk.color)
            pts = [(x * s, y * s) for x, y in sk.points]
            wpx = max(0.5, round(sk.width * s, 3))
            d = polygon_to_d(make_ribbon(pts, wpx))
            comx = sum(p[0] for p in pts) / len(pts)
            comy = sum(p[1] for p in pts) / len(pts)
            ts = hex(sk.timestamp if sk.timestamp else int(time.time() * 1000))
            op = f' fill-opacity="{col[3] / 255:.3f}"' if col[3] < 255 else ""
            lines.append(f'    <path class="write-flat-pen" fill="{c_rgb(col)}"{op} stroke-width="{wpx:g}" '
                         f'__comx="{comx:.3f}" __comy="{comy:.3f}" __timestamp="{ts}" d="{d}" />')
        lines.append('  </g>')
        lines.append('</svg>')
        y_cursor += ph + gap

    thumb_b64 = base64.b64encode(THUMB_PNG).decode("ascii")
    lines += ['<defs id="write-defs">',
              f'<image id="thumbnail" xlink:href="data:image/png;base64,{thumb_b64}"/>',
              '<g id="write-pages">'] + use_tags + ['</g>',
              '<script type="text/writeconfig">',
              '  <int name="docFormatVersion" value="2" />',
              '  <int name="pageNum" value="0" />',
              '  <float name="xOffset" value="0.0" />',
              '  <float name="yOffset" value="0.0" />',
              '</script>',
              '<style type="text/css"><![CDATA[',
              f'  #write-document, #write-doc-background {{ width: {pw + 2 * x_off}px; height: {y_cursor}px; }}',
              ']]></style>', '</defs>', '</svg>']
    with gzip.GzipFile(out_path, "wb", mtime=0) as f:
        f.write("\n".join(lines).encode("utf-8"))


# =====================================================================
# WRITE (.svgz) READER
# =====================================================================
def _local(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def _num(s: Optional[str], default: float = 0.0) -> float:
    if s is None:
        return default
    m = re.match(r"\s*([-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?)", s)
    return float(m.group(1)) if m else default


def _props(el, inh: dict) -> dict:
    p = dict(inh)
    for k in ("fill", "stroke", "stroke-width", "opacity", "fill-opacity", "stroke-opacity"):
        if k in el.attrib:
            p[k] = el.attrib[k]
    style = el.attrib.get("style")
    if style:
        for part in style.split(";"):
            if ":" in part:
                k, v = part.split(":", 1)
                p[k.strip()] = v.strip()
    return p


def ribbon_to_centerline(poly: List[Tuple[float, float]]):
    """Recover (centreline, width) from a closed outline whose vertex i pairs with vertex n-1-i.
    Returns None when the polygon does not look like a pen stroke (caller falls back to outline)."""
    if len(poly) >= 2 and math.hypot(poly[0][0] - poly[-1][0], poly[0][1] - poly[-1][1]) < 1e-6:
        poly = poly[:-1]
    n = len(poly)
    xs, ys = [p[0] for p in poly], [p[1] for p in poly]
    if max(xs) - min(xs) < 4.0 and max(ys) - min(ys) < 4.0:       # a dot
        cx, cy = sum(xs) / n, sum(ys) / n
        r = sum(math.hypot(x - cx, y - cy) for x, y in poly) / n
        return [(cx, cy)], max(2 * r, 0.5)
    if n < 4 or n % 2:
        return None
    half = n // 2
    mids, widths = [], []
    for i in range(half):
        a, b = poly[i], poly[n - 1 - i]
        mids.append(((a[0] + b[0]) / 2, (a[1] + b[1]) / 2))
        widths.append(math.hypot(a[0] - b[0], a[1] - b[1]))
    if max(widths) > 40:
        return None
    out = [mids[0]]
    for m in mids[1:]:
        if math.hypot(m[0] - out[-1][0], m[1] - out[-1][1]) > 1e-3:
            out.append(m)
    return out, sum(widths) / len(widths)


def _decode_data_uri(href: str) -> Optional[bytes]:
    if not href.startswith("data:") or "base64," not in href:
        return None
    try:
        return base64.b64decode(href.split("base64,", 1)[1])
    except Exception:
        return None


def _to_png(data: bytes) -> Optional[bytes]:
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        return data
    if HAVE_PIL:
        try:
            buf = io.BytesIO()
            Image.open(io.BytesIO(data)).convert("RGBA").save(buf, "PNG")
            return buf.getvalue()
        except Exception:
            return None
    return data      # unknown format without Pillow: store as-is; Qt sniffs content, not extension


class _WriteReader:
    def __init__(self, doc: ScrvnDoc, dpi: float):
        self.doc = doc
        self.k = U_PER_INCH / dpi                  # Write px -> Scrivano units
        self.stroke_id = 128
        self.ts = int(time.time() * 1000)
        self.img_cache: Dict[str, str] = {}
        self.n_text = self.n_shapes = 0

    def next_ts(self) -> int:
        self.ts += 7
        return self.ts

    @staticmethod
    def _ts_attr(el) -> int:
        v = el.attrib.get("__timestamp")
        if v:
            try:
                n = int(v, 16) if v.lower().startswith("0x") else int(float(v))
                if n > 0:
                    return n
            except ValueError:
                pass
        return 0

    def walk(self, el, mat: Matrix, inh: dict, page: ScrvnPage):
        for ch in el:
            tag = _local(ch.tag)
            cls = ch.attrib.get("class", "")
            if tag in ("defs", "script", "style", "title", "desc", "metadata") or "ruleline" in cls:
                continue
            m = mat_mul(mat, parse_transform(ch.attrib.get("transform")))
            p = _props(ch, inh)
            if tag == "g" or (tag == "svg" and ch is not el):
                self.walk(ch, m, p, page)
            elif tag == "path":
                self.path(ch, m, p, page)
            elif tag in ("line", "polyline", "polygon"):
                self.simple_shape(ch, tag, m, p, page)
            elif tag == "image":
                self.image(ch, m, page)
            elif tag in ("text", "tspan"):
                self.n_text += 1

    def make_stroke(self, pts_px, width_px, col, ts) -> Stroke:
        a = col[3] / 255.0
        return Stroke(color=c_argb(col[:3] + (int(round(a * 255)),)),
                      width=max(0.3, width_px * self.k),
                      points=[(x * self.k, y * self.k) for x, y in pts_px],
                      timestamp=ts or self.next_ts(), stroke_id=self._sid())

    def _sid(self) -> int:
        self.stroke_id += 1
        return self.stroke_id

    def _alpha(self, col, p, key):
        if col is None:
            return None
        a = col[3] / 255.0 * _num(p.get("opacity"), 1.0) * _num(p.get(key), 1.0)
        return col[:3] + (int(round(max(0.0, min(1.0, a)) * 255)),)

    def path(self, el, m: Matrix, p: dict, page: ScrvnPage):
        d = el.attrib.get("d", "")
        if not d:
            return
        fill = self._alpha(parse_color(p.get("fill", "#000000")), p, "fill-opacity")
        stroke = self._alpha(parse_color(p.get("stroke", "none")), p, "stroke-opacity")
        sc = mat_scale(m)
        ts = self._ts_attr(el)
        subs = parse_path(d)
        if fill and not stroke:                              # Write's pen strokes: filled outlines
            for sub in subs:
                if len(sub) < 2:
                    continue
                poly = [mat_apply(m, x, y) for x, y in sub]
                r = ribbon_to_centerline(poly)
                if r:
                    pts, w = r
                    page.strokes.append(self.make_stroke(pts, w, fill, ts))
                else:                                        # arbitrary filled shape -> keep its outline
                    self.n_shapes += 1
                    page.strokes.append(self.make_stroke(poly + [poly[0]], 1.5, fill, ts))
        elif stroke:                                         # stroked polyline
            w = _num(p.get("stroke-width"), 1.0) * sc
            for sub in subs:
                pts = [mat_apply(m, x, y) for x, y in sub]
                if pts:
                    page.strokes.append(self.make_stroke(pts, w, stroke, ts))

    def simple_shape(self, el, tag, m, p, page):
        if tag == "line":
            pts = [(_num(el.attrib.get("x1")), _num(el.attrib.get("y1"))),
                   (_num(el.attrib.get("x2")), _num(el.attrib.get("y2")))]
        else:
            nums = [float(v) for v in re.findall(r"[-+]?(?:\d+\.?\d*|\.\d+)", el.attrib.get("points", ""))]
            pts = list(zip(nums[0::2], nums[1::2]))
            if tag == "polygon" and pts:
                pts.append(pts[0])
        col = self._alpha(parse_color(p.get("stroke", p.get("fill", "#000000"))), p, "stroke-opacity")
        if col and len(pts) >= 2:
            pts = [mat_apply(m, x, y) for x, y in pts]
            page.strokes.append(self.make_stroke(pts, _num(p.get("stroke-width"), 1.0) * mat_scale(m),
                                                 col, self._ts_attr(el)))

    def image(self, el, m: Matrix, page: ScrvnPage):
        if el.attrib.get("id") == "thumbnail":
            return
        href = el.attrib.get("{http://www.w3.org/1999/xlink}href") or el.attrib.get("href", "")
        raw = _decode_data_uri(href)
        if raw is None:
            self.doc.warnings.append("skipped an <image> that is not an embedded data: URI")
            return
        png = _to_png(raw)
        if png is None:
            self.doc.warnings.append("skipped an image in an unsupported format (install Pillow)")
            return
        x, y = _num(el.attrib.get("x")), _num(el.attrib.get("y"))
        w, h = _num(el.attrib.get("width")), _num(el.attrib.get("height"))
        if w <= 0 or h <= 0:
            pw, ph = get_png_dimensions(png)
            w, h = (pw or 100), (ph or 100)
        corners = [mat_apply(m, cx, cy) for cx, cy in ((x, y), (x + w, y), (x + w, y + h), (x, y + h))]
        xs, ys = [c[0] for c in corners], [c[1] for c in corners]
        if (abs(m[1]) > 1e-6 or abs(m[2]) > 1e-6):         # rotated / skewed: bake into the pixels
            if HAVE_PIL:
                ang = math.degrees(math.atan2(m[1], m[0]))
                im = Image.open(io.BytesIO(png)).convert("RGBA")
                im = im.rotate(-ang, expand=True, resample=Image.BICUBIC)
                buf = io.BytesIO()
                im.save(buf, "PNG")
                png = buf.getvalue()
            else:
                self.doc.warnings.append("a rotated image was stored unrotated (install Pillow to bake rotation)")
        digest = hashlib.sha1(png).hexdigest()
        if digest not in self.img_cache:
            name = "{%s}.png" % uuid.uuid4()
            self.doc.images[name] = png
            self.img_cache[digest] = name
        page.images.append(ImageItem(name=self.img_cache[digest], x=min(xs) * self.k, y=min(ys) * self.k,
                                     w=(max(xs) - min(xs)) * self.k, h=(max(ys) - min(ys)) * self.k,
                                     timestamp=self._ts_attr(el) or self.next_ts()))


def _read_writeconfig(root) -> dict:
    cfg = {}
    for el in root.iter():
        if _local(el.tag) in ("int", "float", "string", "bool") and "name" in el.attrib:
            cfg[el.attrib["name"].lower()] = el.attrib.get("value")
    return cfg


def _int_argb(v) -> Optional[tuple]:
    try:
        n = int(float(v)) & 0xFFFFFFFF
    except (TypeError, ValueError):
        return None
    return ((n >> 16) & 255, (n >> 8) & 255, n & 255, (n >> 24) & 255)


def detect_style(page_el, content, root, dpi: float) -> PaperStyle:
    st = PaperStyle()
    cfg = _read_writeconfig(root)
    pw = _num(page_el.attrib.get("width"), _num(content.attrib.get("width"), 1240.0))
    ph = _num(page_el.attrib.get("height"), _num(content.attrib.get("height"), 1755.0))
    st.size_name, st.width_mm, st.height_mm = match_page_size(pw / dpi * MM_PER_INCH, ph / dpi * MM_PER_INCH)

    def val(attr, cfg_key):
        v = content.attrib.get(attr)
        if v is None:
            v = cfg.get(cfg_key.lower())
        return v

    xr, yr = _num(val("xruling", "xRuling")), _num(val("yruling", "yRuling"))
    ml = _num(val("marginLeft", "marginLeft"))
    pc = parse_color(content.attrib.get("papercolor")) if "papercolor" in content.attrib \
        else _int_argb(cfg.get("pagecolor")) or (255, 255, 255, 255)
    paper = pc[:3] + (255,)
    rc = parse_color(content.attrib.get("rulecolor")) if "rulecolor" in content.attrib \
        else _int_argb(cfg.get("rulecolor")) or (224, 224, 224, 255)
    st.paper_color = c_rgb(paper).lower()
    st.rule_color = c_rgb(blend_on(rc, paper)).lower()

    ruleline = next((e for e in content.iter() if "ruleline" in e.attrib.get("class", "")), None)
    dotted_spacing = None
    if ruleline is not None:
        for e in ruleline.iter():
            if _local(e.tag) == "pattern" and any(_local(c.tag) == "circle" for c in e):
                dotted_spacing = (_num(e.attrib.get("width")), _num(e.attrib.get("height")))
            if "leftmargin" in e.attrib.get("class", "") and "stroke" in e.attrib:
                mc = parse_color(e.attrib["stroke"])
                if mc:
                    st.margin_color = c_rgb(mc).lower()
        if yr <= 0 and xr <= 0 and dotted_spacing is None:      # no attrs: infer from the drawn lines
            hs = []
            for e in ruleline.iter():
                if _local(e.tag) == "path" and "leftmargin" not in e.attrib.get("class", ""):
                    for sub in parse_path(e.attrib.get("d", "")):
                        if len(sub) == 2 and abs(sub[0][1] - sub[1][1]) < 0.5 and abs(sub[0][0] - sub[1][0]) > pw * 0.5:
                            hs.append(sub[0][1])
            hs = sorted(set(hs))
            if len(hs) >= 2:
                yr = sorted(b - a for a, b in zip(hs, hs[1:]))[len(hs) // 2 - 1 if len(hs) > 2 else 0]

    if dotted_spacing and dotted_spacing[0] > 0:
        st.paper_type = PAPER_DOTTED
        st.x_spacing_mm = snap_mm(dotted_spacing[0] / dpi * MM_PER_INCH)
        st.y_spacing_mm = snap_mm(dotted_spacing[1] / dpi * MM_PER_INCH)
    elif xr > 0 and yr > 0:
        st.paper_type = PAPER_GRID
        st.x_spacing_mm, st.y_spacing_mm = snap_mm(xr / dpi * MM_PER_INCH), snap_mm(yr / dpi * MM_PER_INCH)
    elif yr > 0:
        st.paper_type = PAPER_RULED
        st.y_spacing_mm = st.x_spacing_mm = snap_mm(yr / dpi * MM_PER_INCH)
    else:
        st.paper_type = PAPER_BLANK
    st.show_margin = 1 if ml > 0 else 0
    if ml > 0:
        st.margin_mm = snap_mm(ml / dpi * MM_PER_INCH)
    return st


def read_write_svgz(path: str, dpi: float = WRITE_DPI) -> ScrvnDoc:
    doc = ScrvnDoc(title=os.path.splitext(os.path.basename(path))[0])
    raw = open(path, "rb").read()
    if raw[:2] == b"\x1f\x8b":
        raw = gzip.decompress(raw)
    root = ET.fromstring(raw)
    page_els = [e for e in root.iter() if _local(e.tag) == "svg" and "write-page" in e.attrib.get("class", "")]
    if not page_els:
        page_els = [root]
    rd = _WriteReader(doc, dpi)
    for idx, pg in enumerate(page_els):
        content = next((e for e in pg.iter() if "write-content" in e.attrib.get("class", "")), pg)
        if idx == 0:
            doc.style = detect_style(pg, content, root, dpi)
        page = ScrvnPage(uuid_str="{%s}" % uuid.uuid4())
        rd.walk(content, IDENT, {}, page)
        doc.pages.append(page)
    if rd.n_text:
        doc.warnings.append(f"{rd.n_text} text element(s) skipped (text is not converted)")
    if rd.n_shapes:
        doc.warnings.append(f"{rd.n_shapes} filled shape(s) converted to outline strokes")
    return doc


# =====================================================================
# SCRIVANO (.scrvn) WRITER
# =====================================================================
def build_documentinfo(doc: ScrvnDoc) -> bytes:
    s = doc.style
    size_msg = enc_string(1, s.size_name) + enc_float(2, s.width_mm) + enc_float(3, s.height_mm)
    bg = (enc_varint(1, s.paper_type) + enc_float(2, s.x_spacing_mm) + enc_float(3, s.y_spacing_mm) +
          enc_string(4, s.rule_color.lower()) + enc_string(5, s.paper_color.lower()) +
          enc_varint(6, s.show_margin) + enc_float(7, s.margin_mm) +
          enc_string(8, s.margin_color.lower()) + enc_bytes(8, size_msg))
    n = max(1, len(doc.pages))
    # fields 4/5/6: modified-time (ms), min(3, last page) and page count. 4 and 6 are inferred from one sample.
    return (enc_string(1, doc.title) + enc_varint(4, int(time.time() * 1000)) +
            enc_varint(5, min(3, n - 1)) + enc_varint(6, n) +
            enc_bytes(7, enc_varint(1, 1) + enc_bytes(1000, bg)))


def serialize_stroke(st: Stroke, sid: int) -> bytes:
    style = (enc_string(1, st.color) + enc_float(2, st.width) + enc_varint(5, 0) + enc_float(8, 0.5))
    buf = bytearray()
    for x, y in st.points:
        buf += enc_bytes(1, enc_float(1, x) + enc_float(2, y))
    buf += enc_bytes(2, style)
    buf += enc_varint(3, st.timestamp or int(time.time() * 1000))
    buf += enc_varint(4, st.stroke_id or sid)
    buf += enc_varint(5, 1) + enc_varint(6, 1)
    return bytes(buf)


def serialize_image(im: ImageItem) -> bytes:
    rect = enc_float(1, im.x) + enc_float(2, im.y) + enc_float(3, im.w) + enc_float(4, im.h)
    return (enc_string(1, im.name[:-4]) + enc_bytes(2, rect) +
            enc_varint(3, im.timestamp or int(time.time() * 1000)) + enc_float(4, im.extra_f4))


def render_thumbnail(doc: ScrvnDoc, dark: bool = False) -> bytes:
    if not HAVE_PIL or not doc.pages:
        return THUMB_PNG
    st = doc.style
    uw, uh = page_units(st)
    W = 400
    H = int(round(W * uh / uw))
    k = W / uw
    paper = parse_color(st.paper_color, (255, 255, 255, 255))
    img = Image.new("RGBA", (W, H), paper)
    dr = ImageDraw.Draw(img)
    geo = ruling_geometry(st, uw, uh)
    rule = parse_color(st.rule_color, (224, 224, 224, 255))
    for y in geo["h"]:
        dr.line([(0, y * k), (W, y * k)], fill=rule, width=1)
    for x in geo["v"]:
        dr.line([(x * k, 0), (x * k, H)], fill=rule, width=1)
    for x, y in geo["dots"]:
        dr.ellipse([x * k - 1, y * k - 1, x * k + 1, y * k + 1], fill=rule)
    if geo["margin"]:
        dr.line([(geo["margin"] * k, 0), (geo["margin"] * k, H)],
                fill=parse_color(st.margin_color, (219, 84, 75, 255)), width=1)
    page = doc.pages[0]
    for im in page.images:
        try:
            pic = Image.open(io.BytesIO(doc.images[im.name])).convert("RGBA")
            pic = pic.resize((max(1, int(im.w * k)), max(1, int(im.h * k))))
            if 0 <= im.x * k < W and 0 <= im.y * k < H:
                layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
                layer.paste(pic, (int(im.x * k), int(im.y * k)))
                img = Image.alpha_composite(img, layer)
                dr = ImageDraw.Draw(img)
        except Exception:
            pass
    for sk in page.strokes:
        col = parse_color(sk.color)
        pts = [(x * k, y * k) for x, y in sk.points]
        if len(pts) == 1:
            pts = pts * 2
        dr.line(pts, fill=col, width=max(1, int(round(sk.width * k))), joint="curve")
    img = img.convert("RGB")
    if dark:
        img = ImageOps.invert(img)
    buf = io.BytesIO()
    img.convert("RGBA").save(buf, "PNG")
    return buf.getvalue()


def export_to_scrvn(doc: ScrvnDoc, out_path: str):
    with zipfile.ZipFile(out_path, "w", compression=zipfile.ZIP_DEFLATED) as z:
        for name, data in doc.images.items():
            z.writestr(f"images/{name}", data)
        z.writestr("documentinfo", build_documentinfo(doc))
        listbuf = bytearray()
        sid = 128
        for idx, page in enumerate(doc.pages):
            entry = (enc_varint(1, idx) if idx else b"") + enc_string(2, page.uuid_str)
            listbuf += enc_bytes(1, entry)
            pb = bytearray()
            for sk in page.strokes:
                sid += 1
                pb += enc_bytes(1, serialize_stroke(sk, sid))
            for im in page.images:
                if im.name in doc.images:
                    pb += enc_bytes(2, serialize_image(im))
            pb += enc_string(1000, page.uuid_str) + enc_varint(1002, 0)
            z.writestr(f"pages/{page.uuid_str}", bytes(pb))
        z.writestr("pages/pageinfolist", bytes(listbuf))
        z.writestr("thumbnail.png", render_thumbnail(doc, False))
        z.writestr("thumbnail_dark.png", render_thumbnail(doc, True))


# =====================================================================
# XOURNAL++ (.xopp) EXPORTER
# =====================================================================
def _fmt(v: float) -> str:
    return f"{v:.3f}".rstrip("0").rstrip(".") or "0"


def _xopp_line(pts, col, width_pt, cap="round") -> str:
    coords = " ".join(f"{_fmt(x)} {_fmt(y)}" for x, y in pts)
    return f'<stroke tool="pen" color="{c_xopp(col)}" width="{_fmt(width_pt)}" capStyle="{cap}">{coords}</stroke>'


def export_to_xopp(doc: ScrvnDoc, out_path: str, ruling: str = "layer"):
    st = doc.style
    uw, uh = page_units(st)
    pw_pt, ph_pt = uw * PT_PER_U, uh * PT_PER_U
    paper = parse_color(st.paper_color, (255, 255, 255, 255))
    rule = parse_color(st.rule_color, (224, 224, 224, 255))
    mcol = parse_color(st.margin_color, (219, 84, 75, 255))
    geo = ruling_geometry(st, uw, uh)
    P = PT_PER_U

    out = ['<?xml version="1.0" standalone="no"?>',
           '<xournal creator="Xournal++ 1.2.3" fileversion="4">',
           '<title>Xournal++ document - see https://github.com/xournalpp/xournalpp</title>']
    for page in doc.pages:
        out.append(f'<page width="{pw_pt:.8f}" height="{ph_pt:.8f}">')
        if ruling == "native":
            style = {PAPER_BLANK: "plain", PAPER_GRID: "graph", PAPER_DOTTED: "dotted",
                     PAPER_RULED: "lined" if geo["margin"] else "ruled"}.get(st.paper_type, "plain")
            out.append(f'<background type="solid" color="{c_xopp(paper)}" style="{style}"/>')
        else:
            out.append(f'<background type="solid" color="{c_xopp(paper)}" style="plain"/>')
            if geo["h"] or geo["v"] or geo["dots"] or geo["margin"]:
                out.append('<layer name="Ruling">')
                for y in geo["h"]:
                    out.append(_xopp_line([(0, y * P), (pw_pt, y * P)], rule, 1 * P, "butt"))
                for x in geo["v"]:
                    out.append(_xopp_line([(x * P, 0), (x * P, ph_pt)], rule, 1 * P, "butt"))
                for x, y in geo["dots"]:
                    out.append(_xopp_line([(x * P, y * P)] * 2, rule, 2.4 * P, "round"))
                if geo["margin"]:
                    mx = geo["margin"] * P
                    out.append(_xopp_line([(mx, 0), (mx, ph_pt)], mcol, 2 * P, "butt"))
                out.append('</layer>')
        out.append('<layer>')
        for im in page.images:
            data = doc.images.get(im.name)
            if data is None:
                continue
            b64 = base64.b64encode(data).decode("ascii")
            out.append(f'<image left="{_fmt(im.x * P)}" top="{_fmt(im.y * P)}" '
                       f'right="{_fmt((im.x + im.w) * P)}" bottom="{_fmt((im.y + im.h) * P)}">{b64}</image>')
        for sk in page.strokes:
            if not sk.points:
                continue
            col = parse_color(sk.color)
            pts = [(x * P, y * P) for x, y in sk.points]
            if len(pts) == 1:
                pts = pts * 2
            tool_hl = col[3] < 255
            line = _xopp_line(pts, col, sk.width * P)
            if tool_hl:
                line = line.replace('tool="pen"', 'tool="highlighter"', 1)
            out.append(line)
        out.append('</layer>')
        out.append('</page>')
    out.append('</xournal>')
    with gzip.GzipFile(out_path, "wb", mtime=0) as f:
        f.write("\n".join(out).encode("utf-8"))


# =====================================================================
# CLI
# =====================================================================
def load_any(path: str, dpi: float) -> ScrvnDoc:
    with open(path, "rb") as f:
        magic = f.read(4)
    if magic[:2] == b"PK":
        return read_scrvn(path)
    return read_write_svgz(path, dpi)


def summarize(doc: ScrvnDoc, out: str):
    names = {PAPER_BLANK: "blank", PAPER_GRID: "grid", PAPER_RULED: "ruled", PAPER_DOTTED: "dotted"}
    st = doc.style
    print(f"[OK] {len(doc.pages)} pages, {sum(len(p.strokes) for p in doc.pages)} strokes, "
          f"{sum(len(p.images) for p in doc.pages)} images -> {out}")
    print(f"     paper: {names.get(st.paper_type, st.paper_type)}, {st.size_name}, "
          f"spacing {st.x_spacing_mm:g}x{st.y_spacing_mm:g} mm, "
          f"margin {'%g mm' % st.margin_mm if st.show_margin else 'off'}")
    for w in doc.warnings:
        print(f"     warning: {w}")


def main(argv=None):
    ap = argparse.ArgumentParser(description="Convert between Scrivano .scrvn, Stylus Labs Write .svgz and Xournal++ .xopp")
    ap.add_argument("command", choices=["to-write", "to-scrvn", "to-xopp"])
    ap.add_argument("input")
    ap.add_argument("output")
    ap.add_argument("--write-dpi", type=float, default=WRITE_DPI,
                    help="pixels per inch of the Write document (default 150)")
    ap.add_argument("--xopp-ruling", choices=["layer", "native"], default="layer",
                    help="layer: exact ruling on a separate layer (default); native: Xournal++ built-in background")
    a = ap.parse_args(argv)

    if a.command == "to-write":
        doc = read_scrvn(a.input)
        export_to_write_svgz(doc, a.output, a.write_dpi)
    elif a.command == "to-scrvn":
        doc = read_write_svgz(a.input, a.write_dpi)
        export_to_scrvn(doc, a.output)
    else:
        doc = load_any(a.input, a.write_dpi)
        export_to_xopp(doc, a.output, a.xopp_ruling)
    summarize(doc, a.output)


if __name__ == "__main__":
    main()

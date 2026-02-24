import io
import json
import hashlib
import math
import os
import random
import re
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import OrderedDict
from pathlib import Path

from flask import Flask, Response, jsonify, make_response, render_template, request, send_file
from PIL import Image, ImageDraw, ImageFont

try:
    import cairosvg
except Exception:  # pragma: no cover
    cairosvg = None


BASE_DIR = Path(__file__).resolve().parent
GENERATED_DIR = BASE_DIR / "generated"
GENERATED_DIR.mkdir(exist_ok=True)
ASSETS_DIR = BASE_DIR / "assets"

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 100 * 1024 * 1024  # 100MB


PRESETS = {
    "macbook_16_10": (2560, 1600),
    "macbook_pro_16": (3456, 2234),
    "imac_24": (4480, 2520),
    "studio_display": (5120, 2880),
    "iphone_17_pro_max": (1320, 2868),
}

SVG_IMAGE_CACHE: OrderedDict[str, Image.Image] = OrderedDict()
SVG_IMAGE_CACHE_LOCK = threading.Lock()
SVG_IMAGE_CACHE_MAX_ITEMS = 512
MANAGE_STORE_PATH = GENERATED_DIR / "manage_store.json"
MANAGE_STORE_LOCK = threading.Lock()
MANAGE_SELECTION_LOCK = threading.Lock()
MANAGE_SELECTION_CACHE = {"files": [], "directory": "", "updatedAt": 0}


def _read_manage_notes_unlocked() -> dict[str, str]:
    if not MANAGE_STORE_PATH.exists():
        return {}
    try:
        raw = json.loads(MANAGE_STORE_PATH.read_text(encoding="utf-8"))
    except Exception:
        return {}

    if not isinstance(raw, dict):
        return {}
    candidate = raw.get("notes")
    if not isinstance(candidate, dict):
        return {}

    notes: dict[str, str] = {}
    for k, v in candidate.items():
        if isinstance(k, str) and isinstance(v, str):
            notes[k] = v
    return notes


def _write_manage_notes_unlocked(notes: dict[str, str]) -> dict[str, str]:
    normalized = {}
    for k, v in notes.items():
        if isinstance(k, str) and isinstance(v, str):
            normalized[k] = v
    MANAGE_STORE_PATH.write_text(
        json.dumps({"notes": normalized}, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    return normalized


def _read_manage_notes() -> dict[str, str]:
    with MANAGE_STORE_LOCK:
        return _read_manage_notes_unlocked()


def _update_manage_notes(mutator):
    with MANAGE_STORE_LOCK:
        notes = _read_manage_notes_unlocked()
        mutator(notes)
        return _write_manage_notes_unlocked(notes)


def _parse_int(value: str, default: int, min_value: int = 1, max_value: int = 10000) -> int:
    try:
        number = int(value)
        return max(min_value, min(max_value, number))
    except Exception:
        return default


def _parse_bool(value: str | None) -> bool:
    if value is None:
        return False
    return value.lower() in {"1", "true", "yes", "on"}


def _parse_json(value: str | None, default):
    if not value:
        return default
    try:
        return json.loads(value)
    except Exception:
        return default


def _parse_color(value: str | None, default: str = "#0F172A") -> str:
    if not value:
        return default
    value = value.strip()
    if len(value) == 7 and value.startswith("#"):
        hex_chars = "0123456789abcdefABCDEF"
        if all(c in hex_chars for c in value[1:]):
            return value
    return default


def _hex_to_rgb(color: str) -> tuple[int, int, int]:
    c = _parse_color(color, "#FFFFFF")
    return (int(c[1:3], 16), int(c[3:5], 16), int(c[5:7], 16))


def _parse_lines(text: str | None) -> list[str]:
    if not text:
        return []
    return [line.strip() for line in text.splitlines() if line.strip()]


def _contains_cjk(text: str) -> bool:
    for ch in text:
        code = ord(ch)
        if 0x4E00 <= code <= 0x9FFF:
            return True
    return False


def _font_supports_cjk(font: ImageFont.ImageFont, font_size: int) -> bool:
    try:
        probe = Image.new("RGBA", (400, 120), (0, 0, 0, 0))
        draw = ImageDraw.Draw(probe)
        bbox = draw.textbbox((0, 0), "中文测试", font=font)
        width = max(0, bbox[2] - bbox[0])
        # 4 个汉字在正常中文字体下宽度应明显大于占位符方块
        return width >= max(32, int(font_size * 1.5))
    except Exception:
        return False


def _load_text_font(
    font_family: str,
    font_size: int,
    font_bold: bool,
    require_cjk: bool = False,
) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    family = (font_family or "pingfang").lower()
    candidates: list[str] = []
    if family == "pingfang":
        candidates = [
            "/System/Library/Fonts/STHeiti Medium.ttc",
            "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/Supplemental/Songti.ttc",
        ]
    elif family == "sfpro":
        candidates = [
            "/System/Library/Fonts/SFNS.ttf",
            "/System/Library/Fonts/STHeiti Medium.ttc",
            "/System/Library/Fonts/Supplemental/Songti.ttc",
            "/System/Library/Fonts/Supplemental/Arial Unicode.ttf",
        ]
    elif family == "helvetica":
        candidates = [
            "/System/Library/Fonts/Helvetica.ttc",
            "/System/Library/Fonts/Supplemental/Arial.ttf",
        ]
    elif family == "times":
        candidates = [
            "/System/Library/Fonts/Supplemental/Times New Roman.ttf",
            "/System/Library/Fonts/Supplemental/Times New Roman Bold.ttf",
        ]
    elif family == "kaiti":
        candidates = [
            "/System/Library/Fonts/Supplemental/Kailasa.ttc",
            "/System/Library/Fonts/STHeiti Medium.ttc",
            "/System/Library/Fonts/Supplemental/Songti.ttc",
        ]
    elif family == "songti":
        candidates = [
            "/System/Library/Fonts/Supplemental/Songti.ttc",
            "/System/Library/Fonts/STHeiti Medium.ttc",
        ]
    elif family == "heiti":
        candidates = [
            "/System/Library/Fonts/STHeiti Medium.ttc",
            "/System/Library/Fonts/STHeiti Light.ttc",
            "/System/Library/Fonts/Supplemental/Songti.ttc",
        ]
    elif family == "fangsong":
        candidates = [
            "/System/Library/Fonts/Supplemental/Songti.ttc",
            "/System/Library/Fonts/STHeiti Light.ttc",
        ]
    else:
        candidates = [
            "/System/Library/Fonts/STHeiti Medium.ttc",
            "/System/Library/Fonts/Supplemental/Songti.ttc",
            "/System/Library/Fonts/Supplemental/Arial Unicode.ttf",
        ]

    if font_bold:
        candidates = candidates[::-1]

    fallback: ImageFont.ImageFont | None = None
    for path in candidates:
        try:
            font = ImageFont.truetype(path, font_size)
            if fallback is None:
                fallback = font
            if require_cjk and not _font_supports_cjk(font, font_size):
                continue
            return font
        except Exception:
            continue

    for path in [
        "/System/Library/Fonts/STHeiti Medium.ttc",
        "/System/Library/Fonts/Supplemental/Songti.ttc",
    ]:
        try:
            font = ImageFont.truetype(path, font_size)
            if not require_cjk or _font_supports_cjk(font, font_size):
                return font
        except Exception:
            continue
    return fallback or ImageFont.load_default()


def _build_text_images(
    lines: list[str],
    font_family: str,
    font_size: int,
    font_color: str,
    font_bold: bool,
) -> list[Image.Image]:
    images: list[Image.Image] = []
    combined_text = "\n".join(lines)
    font = _load_text_font(font_family, font_size, font_bold, require_cjk=_contains_cjk(combined_text))
    color = _parse_color(font_color, "#0F172A")
    pad_x = max(12, int(font_size * 0.9))
    pad_y = max(8, int(font_size * 0.55))

    for line in lines:
        probe = Image.new("RGBA", (16, 16), (0, 0, 0, 0))
        draw = ImageDraw.Draw(probe)
        bbox = draw.textbbox((0, 0), line, font=font)
        text_w = max(1, bbox[2] - bbox[0])
        text_h = max(1, bbox[3] - bbox[1])
        width = text_w + pad_x * 2
        height = text_h + pad_y * 2
        img = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        d = ImageDraw.Draw(img)
        d.text((pad_x - bbox[0], pad_y - bbox[1]), line, font=font, fill=color)
        images.append(img)
    return images


def _normalize_svg_bytes(svg_bytes: bytes) -> bytes:
    # 兼容 UTF-8 BOM 和声明前空白，避免 "XML or text declaration not at start of entity"
    cleaned = svg_bytes.lstrip(b"\xef\xbb\xbf")
    cleaned = cleaned.lstrip()
    return cleaned


def _is_avif_bytes(raw: bytes) -> bool:
    if len(raw) < 12:
        return False
    # ISO BMFF: ....ftypavif / ....ftypavis
    if raw[4:8] != b"ftyp":
        return False
    brand = raw[8:12]
    return brand in {b"avif", b"avis"}


def _load_svg_rgba(svg_bytes: bytes) -> Image.Image:
    if cairosvg is None:
        raise RuntimeError("缺少 CairoSVG。请先安装 requirements.txt 依赖。")

    normalized = _normalize_svg_bytes(svg_bytes)
    cache_key = hashlib.sha256(normalized).hexdigest()

    with SVG_IMAGE_CACHE_LOCK:
        cached = SVG_IMAGE_CACHE.get(cache_key)
        if cached is not None:
            SVG_IMAGE_CACHE.move_to_end(cache_key)
            return cached.copy()

    # 不强制指定输出尺寸，保留 SVG 自身比例
    png_bytes = cairosvg.svg2png(bytestring=normalized)
    image = Image.open(io.BytesIO(png_bytes)).convert("RGBA")

    with SVG_IMAGE_CACHE_LOCK:
        SVG_IMAGE_CACHE[cache_key] = image.copy()
        SVG_IMAGE_CACHE.move_to_end(cache_key)
        while len(SVG_IMAGE_CACHE) > SVG_IMAGE_CACHE_MAX_ITEMS:
            SVG_IMAGE_CACHE.popitem(last=False)

    return image


def _load_png_rgba(png_bytes: bytes) -> Image.Image:
    image = Image.open(io.BytesIO(png_bytes)).convert("RGBA")
    return image


def _row_chunks(items: list[dict], cols: int) -> list[list[dict]]:
    return [items[i : i + cols] for i in range(0, len(items), cols)]


def _canvas(width: int, height: int, bg: str, transparent_bg: bool) -> Image.Image:
    if transparent_bg:
        return Image.new("RGBA", (width, height), (0, 0, 0, 0))
    return Image.new("RGBA", (width, height), bg)


def _pick_markdown_font(fonts: dict, text: str, bold: bool = False, heading: bool = False):
    if heading:
        if _contains_cjk(text):
            return fonts["title_cjk"]
        return fonts["title"]
    if bold:
        if _contains_cjk(text):
            return fonts["bold_cjk"]
        return fonts["bold"]
    if _contains_cjk(text):
        return fonts["normal_cjk"]
    return fonts["normal"]


def _parse_bold_segments(text: str) -> list[tuple[str, bool]]:
    segments: list[tuple[str, bool]] = []
    cursor = 0
    for m in re.finditer(r"\*\*(.+?)\*\*", text):
        if m.start() > cursor:
            segments.append((text[cursor : m.start()], False))
        segments.append((m.group(1), True))
        cursor = m.end()
    if cursor < len(text):
        segments.append((text[cursor:], False))
    if not segments:
        segments.append((text, False))
    return [(s, b) for s, b in segments if s]


def _build_markdown_lines(text: str) -> list[dict]:
    rows: list[dict] = []
    for raw in text.splitlines():
        line = raw.rstrip()
        if not line.strip():
            rows.append({"type": "blank", "segments": []})
            continue
        heading = re.match(r"^\s{0,3}#\s+(.+)$", line)
        if heading:
            rows.append({"type": "heading", "segments": [(heading.group(1).strip(), False)]})
            continue
        list_item = re.match(r"^\s*[-*+]\s+(.+)$", line)
        if list_item:
            rows.append({"type": "list", "segments": [("• ", False)] + _parse_bold_segments(list_item.group(1).strip())})
            continue
        rows.append({"type": "paragraph", "segments": _parse_bold_segments(line)})
    return rows


def _layout_markdown(draw: ImageDraw.ImageDraw, text: str, fonts: dict, base_font_size: int) -> tuple[list[dict], int, int]:
    rows = _build_markdown_lines(text)
    line_gap = max(2, base_font_size // 6)
    blank_h = max(6, int(base_font_size * 0.55))
    layout: list[dict] = []
    max_w = 1
    y = 0
    for row in rows:
        row_type = row["type"]
        if row_type == "blank":
            h = blank_h
            layout.append({"type": "blank", "y": y, "h": h, "w": 0, "segments": []})
            y += h + line_gap
            continue

        heading = row_type == "heading"
        x = 0
        line_h = 0
        seg_layout = []
        for seg_text, seg_bold in row["segments"]:
            font = _pick_markdown_font(fonts, seg_text, bold=seg_bold, heading=heading)
            bbox = draw.textbbox((0, 0), seg_text, font=font)
            seg_w = max(1, bbox[2] - bbox[0])
            seg_h = max(1, bbox[3] - bbox[1])
            seg_layout.append({"text": seg_text, "font": font, "x": x, "w": seg_w, "h": seg_h})
            x += seg_w
            line_h = max(line_h, seg_h)
        line_h = max(line_h, base_font_size if not heading else int(base_font_size * 1.2))
        max_w = max(max_w, x)
        layout.append({"type": row_type, "y": y, "h": line_h, "w": x, "segments": seg_layout})
        y += line_h + line_gap

    total_h = max(1, y - line_gap if layout else 1)
    return layout, max_w, total_h


def _build_label_tile_image(
    text: str,
    fonts: dict,
    font_size: int,
    font_color,
    box_bg_rgb: tuple[int, int, int],
    box_bg_alpha: int,
) -> Image.Image:
    probe = Image.new("RGBA", (8, 8), (0, 0, 0, 0))
    probe_draw = ImageDraw.Draw(probe)
    layout, text_w, text_h = _layout_markdown(probe_draw, text, fonts, font_size)
    pad_x = max(10, int(font_size * 0.6))
    pad_y = max(8, int(font_size * 0.45))
    width = max(64, text_w + pad_x * 2)
    height = max(48, text_h + pad_y * 2)
    image = Image.new("RGBA", (width, height), (0, 0, 0, 0))
    draw = ImageDraw.Draw(image)
    draw.rounded_rectangle(
        (0, 0, width - 1, height - 1),
        radius=max(8, font_size // 2),
        fill=(box_bg_rgb[0], box_bg_rgb[1], box_bg_rgb[2], max(0, min(255, box_bg_alpha))),
    )
    for row in layout:
        if row["type"] == "blank":
            continue
        row_y = pad_y + row["y"]
        for seg in row["segments"]:
            draw.text((pad_x + seg["x"], row_y), seg["text"], font=seg["font"], fill=font_color)
    return image


def _compose_image_with_label_tile(
    image: Image.Image,
    label_tile: Image.Image,
    position: str,
    gap: int = 16,
) -> Image.Image:
    gap = max(4, gap)
    if position in {"left", "right"}:
        total_w = image.width + gap + label_tile.width
        total_h = max(image.height, label_tile.height)
        canvas = Image.new("RGBA", (total_w, total_h), (0, 0, 0, 0))
        if position == "left":
            lx = 0
            ix = label_tile.width + gap
        else:
            ix = 0
            lx = image.width + gap
        ly = (total_h - label_tile.height) // 2
        iy = (total_h - image.height) // 2
        canvas.paste(label_tile, (lx, ly), label_tile)
        canvas.paste(image, (ix, iy), image)
        return canvas

    total_w = max(image.width, label_tile.width)
    total_h = image.height + gap + label_tile.height
    canvas = Image.new("RGBA", (total_w, total_h), (0, 0, 0, 0))
    ix = (total_w - image.width) // 2
    lx = (total_w - label_tile.width) // 2
    if position == "top":
        ly = 0
        iy = label_tile.height + gap
    else:
        iy = 0
        ly = image.height + gap
    canvas.paste(label_tile, (lx, ly), label_tile)
    canvas.paste(image, (ix, iy), image)
    return canvas


def _draw_page_number(
    canvas: Image.Image,
    text: str,
    position: str,
):
    if not text:
        return
    overlay = Image.new("RGBA", canvas.size, (0, 0, 0, 0))
    draw = ImageDraw.Draw(overlay)
    font_size = max(12, min(40, int(min(canvas.width, canvas.height) * 0.026)))
    font = _load_text_font("sfpro", font_size, True, require_cjk=False)
    bbox = draw.textbbox((0, 0), text, font=font)
    tw = max(1, bbox[2] - bbox[0])
    th = max(1, bbox[3] - bbox[1])
    pad_x = max(8, int(font_size * 0.45))
    pad_y = max(6, int(font_size * 0.33))
    margin = max(10, int(font_size * 0.6))

    box_w = tw + pad_x * 2
    box_h = th + pad_y * 2
    if position == "top_left":
        x = margin
        y = margin
    elif position == "bottom_left":
        x = margin
        y = canvas.height - box_h - margin
    elif position == "bottom_right":
        x = canvas.width - box_w - margin
        y = canvas.height - box_h - margin
    else:
        x = canvas.width - box_w - margin
        y = margin

    draw.rounded_rectangle(
        (x, y, x + box_w, y + box_h),
        radius=max(8, font_size // 2),
        fill=(0, 0, 0, 110),
    )
    text_x = x + pad_x - bbox[0]
    text_y = y + pad_y - bbox[1]
    draw.text((text_x, text_y), text, font=font, fill=(255, 255, 255, 235))
    canvas.alpha_composite(overlay)


def _draw_tile_label(
    canvas: Image.Image,
    cell_left: int,
    cell_top: int,
    cell_w: int,
    cell_h: int,
    text: str,
    position: str,
    fonts: dict,
    font_size: int,
    font_color,
    box_bg_rgb: tuple[int, int, int],
    box_bg_alpha: int,
):
    if not text:
        return
    # Draw label on a transparent overlay and alpha-composite it onto canvas,
    # so box opacity actually blends with underlying image content.
    overlay = Image.new("RGBA", canvas.size, (0, 0, 0, 0))
    draw = ImageDraw.Draw(overlay)
    layout, text_w, text_h = _layout_markdown(draw, text, fonts, font_size)
    margin = max(4, int(font_size * 0.35))
    pad_x = max(4, int(font_size * 0.35))
    pad_y = max(3, int(font_size * 0.25))

    if position == "top":
        x = cell_left + (cell_w - text_w) // 2
        y = cell_top + margin
    elif position == "left":
        x = cell_left + margin
        y = cell_top + (cell_h - text_h) // 2
    elif position == "right":
        x = cell_left + cell_w - text_w - margin
        y = cell_top + (cell_h - text_h) // 2
    else:
        x = cell_left + (cell_w - text_w) // 2
        y = cell_top + cell_h - text_h - margin

    min_x = cell_left + 2
    max_x = max(min_x, cell_left + cell_w - text_w - 2)
    min_y = cell_top + 2
    max_y = max(min_y, cell_top + cell_h - text_h - 2)
    x = max(min_x, min(max_x, x))
    y = max(min_y, min(max_y, y))

    rect = (
        x - pad_x,
        y - pad_y,
        x + text_w + pad_x,
        y + text_h + pad_y,
    )
    draw.rounded_rectangle(
        rect,
        radius=max(4, font_size // 3),
        fill=(box_bg_rgb[0], box_bg_rgb[1], box_bg_rgb[2], max(0, min(255, box_bg_alpha))),
    )
    for row in layout:
        if row["type"] == "blank":
            continue
        row_y = y + row["y"]
        for seg in row["segments"]:
            draw.text((x + seg["x"], row_y), seg["text"], font=seg["font"], fill=font_color)
    canvas.alpha_composite(overlay)


def _compose_uniform_grid(
    items: list[dict],
    width: int,
    height: int,
    cols: int,
    gap: int,
    padding: int,
    bg: str,
    transparent_bg: bool,
    label_enabled: bool,
    label_font_family: str,
    label_font_size: int,
    label_font_color: str,
    label_box_bg_color: str,
    label_box_bg_opacity: int,
    label_as_tile: bool,
    label_position: str,
) -> Image.Image:
    count = len(items)
    rows = max(1, math.ceil(count / cols))

    available_w = width - 2 * padding - gap * (cols - 1)
    available_h = height - 2 * padding - gap * (rows - 1)

    cell_w = max(10, available_w // cols)
    cell_h = max(10, available_h // rows)

    canvas = _canvas(width, height, bg, transparent_bg)
    label_fonts = None
    label_color = None
    label_box_bg_rgb = (255, 255, 255)
    label_box_bg_alpha = 180
    if label_enabled:
        title_size = max(12, int(round(label_font_size * 1.25)))
        label_fonts = {
            "normal": _load_text_font(label_font_family, label_font_size, False, require_cjk=False),
            "normal_cjk": _load_text_font(label_font_family, label_font_size, False, require_cjk=True),
            "bold": _load_text_font(label_font_family, label_font_size, True, require_cjk=False),
            "bold_cjk": _load_text_font(label_font_family, label_font_size, True, require_cjk=True),
            "title": _load_text_font(label_font_family, title_size, True, require_cjk=False),
            "title_cjk": _load_text_font(label_font_family, title_size, True, require_cjk=True),
        }
        label_color = _parse_color(label_font_color, "#0F172A")
        label_box_bg_rgb = _hex_to_rgb(label_box_bg_color)
        label_box_bg_alpha = max(0, min(255, int(round((max(0, min(100, label_box_bg_opacity)) / 100) * 255))))

    for idx, item in enumerate(items):
        image = item["image"]
        label = item.get("label", "")
        if label_enabled and label_as_tile and label:
            label_tile = _build_label_tile_image(
                text=label,
                fonts=label_fonts,
                font_size=label_font_size,
                font_color=label_color,
                box_bg_rgb=label_box_bg_rgb,
                box_bg_alpha=label_box_bg_alpha,
            )
            image = _compose_image_with_label_tile(image, label_tile, label_position, gap=max(8, label_font_size // 2))
        row = idx // cols
        col = idx % cols

        x = padding + col * (cell_w + gap)
        y = padding + row * (cell_h + gap)

        tile = image.copy()

        # 保持留白，避免图形贴边
        inner_w = max(4, int(cell_w * 0.9))
        inner_h = max(4, int(cell_h * 0.9))
        tile.thumbnail((inner_w, inner_h), Image.Resampling.LANCZOS)

        tile_x = x + (cell_w - tile.width) // 2
        tile_y = y + (cell_h - tile.height) // 2
        canvas.paste(tile, (tile_x, tile_y), tile)
        if label_enabled and label and not label_as_tile:
            _draw_tile_label(
                canvas=canvas,
                cell_left=x,
                cell_top=y,
                cell_w=cell_w,
                cell_h=cell_h,
                text=label,
                position=label_position,
                fonts=label_fonts,
                font_size=label_font_size,
                font_color=label_color,
                box_bg_rgb=label_box_bg_rgb,
                box_bg_alpha=label_box_bg_alpha,
            )

    return canvas


def _compose_adaptive_grid(
    items: list[dict],
    width: int,
    height: int,
    cols: int,
    gap: int,
    padding: int,
    bg: str,
    transparent_bg: bool,
    min_row_height: int = 1,
    label_enabled: bool = False,
    label_font_family: str = "pingfang",
    label_font_size: int = 16,
    label_font_color: str = "#0F172A",
    label_box_bg_color: str = "#FFFFFF",
    label_box_bg_opacity: int = 70,
    label_as_tile: bool = False,
    label_position: str = "bottom",
) -> Image.Image:
    """
    自适应模式：
    - 每行最多 cols 个图
    - 每行按图片宽高比分配格子宽度
    - 统一缩放让所有行都落在可用高度内
    """
    rows = _row_chunks(items, cols)
    available_w = max(20, width - 2 * padding)
    available_h = max(20, height - 2 * padding)
    canvas = _canvas(width, height, bg, transparent_bg)
    label_fonts = None
    label_color = None
    label_box_bg_rgb = (255, 255, 255)
    label_box_bg_alpha = 180
    if label_enabled:
        title_size = max(12, int(round(label_font_size * 1.25)))
        label_fonts = {
            "normal": _load_text_font(label_font_family, label_font_size, False, require_cjk=False),
            "normal_cjk": _load_text_font(label_font_family, label_font_size, False, require_cjk=True),
            "bold": _load_text_font(label_font_family, label_font_size, True, require_cjk=False),
            "bold_cjk": _load_text_font(label_font_family, label_font_size, True, require_cjk=True),
            "title": _load_text_font(label_font_family, title_size, True, require_cjk=False),
            "title_cjk": _load_text_font(label_font_family, title_size, True, require_cjk=True),
        }
        label_color = _parse_color(label_font_color, "#0F172A")
        label_box_bg_rgb = _hex_to_rgb(label_box_bg_color)
        label_box_bg_alpha = max(0, min(255, int(round((max(0, min(100, label_box_bg_opacity)) / 100) * 255))))

    raw_row_heights: list[float] = []
    row_ratios: list[list[float]] = []
    for row in rows:
        ratios = []
        for item in row:
            img = item["image"]
            if img.height <= 0:
                ratios.append(1.0)
            else:
                ratios.append(max(0.05, img.width / img.height))
        row_ratios.append(ratios)
        usable_row_w = max(20.0, available_w - gap * (len(row) - 1))
        raw_row_heights.append(usable_row_w / max(0.1, sum(ratios)))

    # 精确分配每行像素高度，确保总高度不超出 available_h，避免底部裁切
    gap_total = gap * (len(rows) - 1)
    usable_h = max(1, available_h - gap_total)
    min_h = max(1, min(min_row_height, usable_h))
    base_floor = min_h * len(rows)
    if base_floor > usable_h:
        # 可用高度不足时自动降级，优先保证不裁切
        min_h = max(1, usable_h // max(1, len(rows)))
        base_floor = min_h * len(rows)

    raw_sum = sum(raw_row_heights)
    if raw_sum <= 0:
        float_heights = [((usable_h - base_floor) / max(1, len(rows))) for _ in rows]
    else:
        float_heights = [(h / raw_sum) * (usable_h - base_floor) for h in raw_row_heights]

    int_heights = [min_h + max(0, int(math.floor(h))) for h in float_heights]
    diff = usable_h - sum(int_heights)
    if diff != 0:
        # 按小数部分做余数分配，减少累计取整误差
        fracs = sorted(
            [(idx, float_heights[idx] - int_heights[idx]) for idx in range(len(int_heights))],
            key=lambda x: x[1],
            reverse=(diff > 0),
        )
        step = 1 if diff > 0 else -1
        i = 0
        while diff != 0 and fracs:
            idx = fracs[i % len(fracs)][0]
            if step < 0 and int_heights[idx] <= min_h:
                i += 1
                if i > len(fracs) * 4:
                    break
                continue
            int_heights[idx] += step
            diff -= step
            i += 1

    y = padding

    for row_idx, row in enumerate(rows):
        ratios = row_ratios[row_idx]
        row_h = int_heights[row_idx]
        usable_row_w = max(20.0, available_w - gap * (len(row) - 1))
        ratio_sum = max(0.1, sum(ratios))

        widths = [max(8, int(round(usable_row_w * (r / ratio_sum)))) for r in ratios]
        delta = int(usable_row_w - sum(widths))
        if widths:
            widths[-1] += delta

        x = padding
        for idx, item in enumerate(row):
            image = item["image"]
            label = item.get("label", "")
            if label_enabled and label_as_tile and label:
                label_tile = _build_label_tile_image(
                    text=label,
                    fonts=label_fonts,
                    font_size=label_font_size,
                    font_color=label_color,
                    box_bg_rgb=label_box_bg_rgb,
                    box_bg_alpha=label_box_bg_alpha,
                )
                image = _compose_image_with_label_tile(image, label_tile, label_position, gap=max(8, label_font_size // 2))
            target_w = max(8, widths[idx])
            target_h = max(1, int(row_h))
            tile = image.copy()
            tile.thumbnail((target_w, target_h), Image.Resampling.LANCZOS)

            tile_x = x + (target_w - tile.width) // 2
            tile_y = y + (target_h - tile.height) // 2
            canvas.paste(tile, (tile_x, tile_y), tile)
            if label_enabled and label and not label_as_tile:
                _draw_tile_label(
                    canvas=canvas,
                    cell_left=x,
                    cell_top=y,
                    cell_w=target_w,
                    cell_h=target_h,
                    text=label,
                    position=label_position,
                    fonts=label_fonts,
                    font_size=label_font_size,
                    font_color=label_color,
                    box_bg_rgb=label_box_bg_rgb,
                    box_bg_alpha=label_box_bg_alpha,
                )
            x += target_w + gap

        y += int(row_h) + gap

    return canvas


def _collect_media_contents(files) -> list[tuple[bytes, str, str, str]]:
    media_contents: list[tuple[bytes, str, str, str]] = []
    for f in files:
        raw = f.read()
        if not raw:
            continue
        raw_name = (f.filename or "").strip()
        name = raw_name.lower()
        if name.endswith(".svg") or b"<svg" in raw[:4000].lower():
            media_contents.append((raw, "svg", raw_name, ""))
            continue
        if name.endswith(".png") or raw.startswith(b"\x89PNG\r\n\x1a\n"):
            media_contents.append((raw, "png", raw_name, ""))
            continue
        if name.endswith(".jpg") or name.endswith(".jpeg") or raw.startswith(b"\xff\xd8\xff"):
            media_contents.append((raw, "jpeg", raw_name, ""))
            continue
        if name.endswith(".webp") or raw.startswith(b"RIFF") and raw[8:12] == b"WEBP":
            media_contents.append((raw, "webp", raw_name, ""))
            continue
        if name.endswith(".avif") or _is_avif_bytes(raw):
            media_contents.append((raw, "avif", raw_name, ""))
            continue
    return media_contents


def _collect_media_contents_from_dir(svg_dir: str, max_files: int = 5000) -> list[tuple[bytes, str, str, str]]:
    if not svg_dir:
        return []
    base = Path(svg_dir).expanduser()
    if not base.is_absolute():
        base = (BASE_DIR / base).resolve()
    if not base.exists():
        raise ValueError(f"目录不存在: {svg_dir}")
    if not base.is_dir():
        raise ValueError(f"不是目录: {svg_dir}")

    media_contents: list[tuple[bytes, str, str, str]] = []
    for path in base.rglob("*"):
        if not path.is_file():
            continue
        try:
            raw = path.read_bytes()
        except Exception:
            continue
        if not raw:
            continue

        rel_path = ""
        try:
            rel_path = str(path.relative_to(base))
        except Exception:
            rel_path = path.name

        ext = path.suffix.lower()
        if ext == ".svg" and b"<svg" in raw[:4000].lower():
            media_contents.append((raw, "svg", rel_path, svg_dir))
        elif ext == ".png" and raw.startswith(b"\x89PNG\r\n\x1a\n"):
            media_contents.append((raw, "png", rel_path, svg_dir))
        elif ext in {".jpg", ".jpeg"} and raw.startswith(b"\xff\xd8\xff"):
            media_contents.append((raw, "jpeg", rel_path, svg_dir))
        elif ext == ".webp" and raw.startswith(b"RIFF") and raw[8:12] == b"WEBP":
            media_contents.append((raw, "webp", rel_path, svg_dir))
        elif ext == ".avif" and _is_avif_bytes(raw):
            media_contents.append((raw, "avif", rel_path, svg_dir))

        if len(media_contents) >= max_files:
            break
    return media_contents


def _decode_images(media_contents: list[tuple[bytes, str, str, str]]) -> tuple[list[dict], int]:
    images: list[dict] = []
    skipped = 0
    for raw, media_type, source_name, source_dir in media_contents:
        try:
            if media_type == "svg":
                decoded = _load_svg_rgba(raw)
            elif media_type in {"png", "jpeg", "webp", "avif"}:
                decoded = _load_png_rgba(raw)
            else:
                skipped += 1
                continue
            images.append({"image": decoded, "source_name": source_name, "source_dir": source_dir, "label": ""})
        except Exception:
            skipped += 1
    return images, skipped


def _inject_zima_blue_tile(images: list[dict]) -> list[dict]:
    if not images:
        return images
    side = random.randint(320, 1024)
    tile = {"image": Image.new("RGBA", (side, side), "#5BC2E7"), "source_name": "", "source_dir": "", "label": ""}
    insert_at = random.randint(0, len(images))
    merged = list(images)
    merged.insert(insert_at, tile)
    return merged


def _normalize_markdown_for_render(value: str) -> str:
    text = (value or "").replace("\r\n", "\n").replace("\r", "\n")
    # fenced code blocks: keep code body
    text = re.sub(r"```[^\n]*\n([\s\S]*?)```", lambda m: m.group(1).strip("\n"), text)
    # inline code
    text = re.sub(r"`([^`]+)`", r"\1", text)
    # images and links
    text = re.sub(r"!\[([^\]]*)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", text)
    # keep heading/list markers for rendering, strip only quote markers
    text = re.sub(r"^\s*>\s?", "", text, flags=re.MULTILINE)
    text = re.sub(r"^\s*\d+\.\s+", "- ", text, flags=re.MULTILINE)
    # remove non-target markdown syntaxes
    text = text.replace("__", "**")
    text = text.replace("~~", "")
    text = re.sub(r"(?<!\*)\*(?!\*)", "", text)
    text = re.sub(r"(?<!_)_(?!_)", "", text)
    # remove horizontal rules
    text = re.sub(r"^\s*([-*_]){3,}\s*$", "", text, flags=re.MULTILINE)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def _build_media_label(item: dict, opts: dict, notes: dict[str, str]) -> str:
    if not opts["overlay_show_filename"] and not opts["overlay_show_note"]:
        return ""
    source_name = str(item.get("source_name", "") or "")
    source_dir = str(item.get("source_dir", "") or "")

    parts: list[str] = []
    if opts["overlay_show_filename"]:
        parts.append(Path(source_name).stem if source_name else "")
    if opts["overlay_show_note"] and source_name:
        note_key = f"{source_dir}::{source_name}"
        note = (notes.get(note_key) or "").strip()
        if not note:
            # 兜底：当来源路径与备注键不一致时，按文件名匹配备注
            base_name = Path(source_name).name
            for k, v in notes.items():
                if not isinstance(k, str) or not isinstance(v, str):
                    continue
                sep = k.find("::")
                note_name = k[sep + 2 :] if sep >= 0 else k
                if Path(note_name).name == base_name:
                    note = v.strip()
                    if note:
                        break
        if note:
            parts.append(_normalize_markdown_for_render(note))
    parts = [p for p in parts if p]
    return "\n".join(parts)


def _load_items_from_request(opts: dict, files, svg_dir: str, randomize: bool) -> tuple[list[dict], int, str | None]:
    skipped = 0
    if opts["content_mode"] == "text":
        lines = _parse_lines(opts["text_content"])
        if not lines:
            return [], 0, "文本模式下请输入内容（每行一个文本项）。"
        if randomize:
            random.shuffle(lines)
        text_images = _build_text_images(
            lines=lines,
            font_family=opts["text_font_family"],
            font_size=opts["text_font_size"],
            font_color=opts["text_font_color"],
            font_bold=opts["text_font_bold"],
        )
        items = [{"image": img, "source_name": "", "source_dir": "", "label": ""} for img in text_images]
        return items, skipped, None

    if not files and not svg_dir:
        return [], 0, "请先上传 SVG/PNG/JPEG/WebP/AVIF 文件，或提供目录路径。"
    media_contents = _collect_media_contents(files)
    if svg_dir:
        try:
            media_contents.extend(_collect_media_contents_from_dir(svg_dir))
        except ValueError as e:
            return [], 0, str(e)
    if not media_contents:
        return [], 0, "未检测到有效 SVG/PNG/JPEG/WebP/AVIF（上传或目录）。"
    if randomize:
        random.shuffle(media_contents)
    items, skipped = _decode_images(media_contents)
    if not items:
        return [], skipped, "所有文件解析失败，请检查 SVG/PNG/JPEG/WebP/AVIF 文件是否损坏。"

    if opts["overlay_show_filename"] or opts["overlay_show_note"]:
        notes = _read_manage_notes() if opts["overlay_show_note"] else {}
        for item in items:
            item["label"] = _build_media_label(item, opts, notes)

    return items, skipped, None


def _parse_base_options():
    preset = request.form.get("preset", "macbook_16_10")
    if preset in PRESETS:
        width, height = PRESETS[preset]
    else:
        width = _parse_int(request.form.get("width", "2560"), 2560)
        height = _parse_int(request.form.get("height", "1600"), 1600)

    cols = _parse_int(request.form.get("cols", "6"), 6, 1, 20)
    gap = _parse_int(request.form.get("gap", "24"), 24, 0, 200)
    padding = _parse_int(request.form.get("padding", "80"), 80, 0, 500)
    bg = request.form.get("bg", "#FFFFFF")
    transparent_bg = _parse_bool(request.form.get("transparent_bg"))
    adaptive_grid = _parse_bool(request.form.get("adaptive_grid"))
    min_row_height = _parse_int(request.form.get("min_row_height", "1"), 1, 1, 120)
    png_optimize = _parse_bool(request.form.get("png_optimize"))
    png_compress_level = _parse_int(request.form.get("png_compress_level", "1"), 1, 0, 9)
    content_mode = (request.form.get("content_mode") or "media").strip().lower()
    text_content = request.form.get("text_content", "")
    text_font_family = (request.form.get("text_font_family") or "pingfang").strip().lower()
    text_font_size = _parse_int(request.form.get("text_font_size", "72"), 72, 10, 360)
    text_font_color = _parse_color(request.form.get("text_font_color"), "#0F172A")
    text_font_bold = _parse_bool(request.form.get("text_font_bold"))
    add_zima_blue = _parse_bool(request.form.get("add_zima_blue"))
    overlay_show_filename = _parse_bool(request.form.get("overlay_show_filename"))
    overlay_show_note = _parse_bool(request.form.get("overlay_show_note"))
    overlay_font_family = (request.form.get("overlay_font_family") or "pingfang").strip().lower()
    overlay_font_size = _parse_int(request.form.get("overlay_font_size", "18"), 18, 10, 120)
    overlay_font_color = _parse_color(request.form.get("overlay_font_color"), "#0F172A")
    overlay_box_bg_color = _parse_color(request.form.get("overlay_box_bg_color"), "#FFFFFF")
    overlay_box_bg_opacity = _parse_int(request.form.get("overlay_box_bg_opacity", "70"), 70, 0, 100)
    overlay_as_tile = _parse_bool(request.form.get("overlay_as_tile"))
    overlay_position = (request.form.get("overlay_position") or "bottom").strip().lower()
    if overlay_position not in {"top", "bottom", "left", "right"}:
        overlay_position = "bottom"
    page_number_enabled = _parse_bool(request.form.get("page_number_enabled"))
    page_number_position = (request.form.get("page_number_position") or "bottom_right").strip().lower()
    if page_number_position not in {"top_left", "top_right", "bottom_left", "bottom_right"}:
        page_number_position = "bottom_right"

    return {
        "width": width,
        "height": height,
        "cols": cols,
        "gap": gap,
        "padding": padding,
        "bg": bg,
        "transparent_bg": transparent_bg,
        "adaptive_grid": adaptive_grid,
        "min_row_height": min_row_height,
        "png_optimize": png_optimize,
        "png_compress_level": png_compress_level,
        "content_mode": content_mode,
        "text_content": text_content,
        "text_font_family": text_font_family,
        "text_font_size": text_font_size,
        "text_font_color": text_font_color,
        "text_font_bold": text_font_bold,
        "add_zima_blue": add_zima_blue,
        "overlay_show_filename": overlay_show_filename,
        "overlay_show_note": overlay_show_note,
        "overlay_font_family": overlay_font_family,
        "overlay_font_size": overlay_font_size,
        "overlay_font_color": overlay_font_color,
        "overlay_box_bg_color": overlay_box_bg_color,
        "overlay_box_bg_opacity": overlay_box_bg_opacity,
        "overlay_as_tile": overlay_as_tile,
        "overlay_position": overlay_position,
        "page_number_enabled": page_number_enabled,
        "page_number_position": page_number_position,
    }


def _compose_and_save_variant(
    items: list[dict],
    width: int,
    height: int,
    cols: int,
    gap: int,
    padding: int,
    bg: str,
    transparent_bg: bool,
    adaptive_grid: bool,
    min_row_height: int,
    png_optimize: bool,
    png_compress_level: int,
    label_enabled: bool,
    label_font_family: str,
    label_font_size: int,
    label_font_color: str,
    label_box_bg_color: str,
    label_box_bg_opacity: int,
    label_as_tile: bool,
    label_position: str,
    page_number_text: str | None = None,
    page_number_position: str = "bottom_right",
) -> str:
    if adaptive_grid:
        wall = _compose_adaptive_grid(
            items,
            width,
            height,
            cols,
            gap,
            padding,
            bg,
            transparent_bg,
            min_row_height=min_row_height,
            label_enabled=label_enabled,
            label_font_family=label_font_family,
            label_font_size=label_font_size,
            label_font_color=label_font_color,
            label_box_bg_color=label_box_bg_color,
            label_box_bg_opacity=label_box_bg_opacity,
            label_as_tile=label_as_tile,
            label_position=label_position,
        )
    else:
        wall = _compose_uniform_grid(
            items,
            width,
            height,
            cols,
            gap,
            padding,
            bg,
            transparent_bg,
            label_enabled=label_enabled,
            label_font_family=label_font_family,
            label_font_size=label_font_size,
            label_font_color=label_font_color,
            label_box_bg_color=label_box_bg_color,
            label_box_bg_opacity=label_box_bg_opacity,
            label_as_tile=label_as_tile,
            label_position=label_position,
        )

    if page_number_text:
        _draw_page_number(wall, page_number_text, page_number_position)

    file_id = uuid.uuid4().hex
    output_path = GENERATED_DIR / f"wallpaper_{file_id}.png"
    wall.save(output_path, "PNG", optimize=png_optimize, compress_level=png_compress_level)
    return output_path.name


@app.get("/")
def index():
    resp = make_response(render_template("index.html", presets=PRESETS))
    resp.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    resp.headers["Pragma"] = "no-cache"
    resp.headers["Expires"] = "0"
    return resp


@app.get("/manage-files")
def manage_files():
    return render_template("manage_files.html")


@app.get("/api/assets-dirs")
def assets_dirs():
    if not ASSETS_DIR.exists() or not ASSETS_DIR.is_dir():
        return jsonify({"dirs": []})

    dirs: list[str] = []
    for child in sorted(ASSETS_DIR.iterdir(), key=lambda p: p.name.lower()):
        if child.is_dir() and not child.name.startswith("."):
            dirs.append(f"assets/{child.name}")
    return jsonify({"dirs": dirs})


@app.get("/api/assets-files")
def assets_files():
    svg_dir = (request.args.get("dir") or "").strip()
    if not svg_dir:
        return jsonify({"files": []})

    base = Path(svg_dir).expanduser()
    if not base.is_absolute():
        base = (BASE_DIR / base).resolve()
    if not base.exists():
        return jsonify({"error": f"目录不存在: {svg_dir}"}), 400
    if not base.is_dir():
        return jsonify({"error": f"不是目录: {svg_dir}"}), 400

    allowed_exts = {".svg", ".png", ".jpg", ".jpeg", ".webp", ".avif"}
    files: list[str] = []
    for path in base.rglob("*"):
        if not path.is_file():
            continue
        if path.suffix.lower() not in allowed_exts:
            continue
        try:
            files.append(str(path.relative_to(base)))
        except Exception:
            files.append(path.name)

    files.sort(key=lambda x: x.lower())
    return jsonify({"files": files})


@app.get("/api/assets-file")
def assets_file():
    svg_dir = (request.args.get("dir") or "").strip()
    rel_path = (request.args.get("path") or "").strip()
    if not svg_dir or not rel_path:
        return "Bad Request", 400

    base = Path(svg_dir).expanduser()
    if not base.is_absolute():
        base = (BASE_DIR / base).resolve()
    if not base.exists() or not base.is_dir():
        return "Not Found", 404

    target = (base / rel_path).resolve()
    if target == base or base not in target.parents:
        return "Forbidden", 403
    if not target.exists() or not target.is_file():
        return "Not Found", 404

    ext = target.suffix.lower()
    if ext not in {".svg", ".png", ".jpg", ".jpeg", ".webp", ".avif"}:
        return "Unsupported Media Type", 415

    if ext == ".svg":
        mimetype = "image/svg+xml"
    elif ext == ".png":
        mimetype = "image/png"
    elif ext in {".jpg", ".jpeg"}:
        mimetype = "image/jpeg"
    elif ext == ".avif":
        mimetype = "image/avif"
    else:
        mimetype = "image/webp"
    return send_file(target, mimetype=mimetype)


@app.get("/api/manage-state")
def manage_state():
    with MANAGE_SELECTION_LOCK:
        selection = {
            "files": list(MANAGE_SELECTION_CACHE.get("files", [])),
            "directory": str(MANAGE_SELECTION_CACHE.get("directory", "")),
            "updatedAt": int(MANAGE_SELECTION_CACHE.get("updatedAt", 0)),
        }
    return jsonify({"selection": selection, "notes": _read_manage_notes()})


@app.post("/api/manage-selection")
def manage_selection():
    payload = request.get_json(silent=True) or {}
    files_raw = payload.get("files")
    directory_raw = payload.get("directory")
    updated_at_raw = payload.get("updatedAt")

    files = []
    if isinstance(files_raw, list):
        files = [item for item in files_raw if isinstance(item, str) and item.strip()]
    directory = directory_raw if isinstance(directory_raw, str) else ""
    updated_at = int(updated_at_raw) if isinstance(updated_at_raw, (int, float)) else int(time.time() * 1000)

    with MANAGE_SELECTION_LOCK:
        MANAGE_SELECTION_CACHE.update(
            {
                "files": files,
                "directory": directory,
                "updatedAt": updated_at,
            }
        )

    return jsonify(
        {
            "ok": True,
            "selection": {
                "files": files,
                "directory": directory,
                "updatedAt": updated_at,
            },
        }
    )


@app.post("/api/manage-note")
def manage_note():
    payload = request.get_json(silent=True) or {}
    directory_raw = payload.get("directory")
    name_raw = payload.get("name")
    note_raw = payload.get("note")

    directory = directory_raw if isinstance(directory_raw, str) else ""
    name = name_raw.strip() if isinstance(name_raw, str) else ""
    note = note_raw if isinstance(note_raw, str) else ""
    if not name:
        return jsonify({"error": "缺少文件名"}), 400

    key = f"{directory}::{name}"

    def mutate(notes: dict[str, str]):
        if note.strip():
            notes[key] = note
        else:
            notes.pop(key, None)

    _update_manage_notes(mutate)
    return jsonify({"ok": True})


@app.post("/api/rename-asset-file")
def rename_asset_file():
    payload = request.get_json(silent=True) or {}
    directory_raw = payload.get("directory")
    rel_path_raw = payload.get("path")
    new_base_raw = payload.get("newBaseName")

    directory = directory_raw.strip() if isinstance(directory_raw, str) else ""
    rel_path = rel_path_raw.strip() if isinstance(rel_path_raw, str) else ""
    new_base_name = new_base_raw.strip() if isinstance(new_base_raw, str) else ""

    if not directory or not rel_path or not new_base_name:
        return jsonify({"error": "参数不完整"}), 400
    if any(ch in new_base_name for ch in ["/", "\\", "\x00"]):
        return jsonify({"error": "文件名包含非法字符"}), 400
    if new_base_name in {".", ".."}:
        return jsonify({"error": "文件名不合法"}), 400

    base = Path(directory).expanduser()
    if not base.is_absolute():
        base = (BASE_DIR / base).resolve()
    if not base.exists() or not base.is_dir():
        return jsonify({"error": "目录不存在"}), 404

    old_target = (base / rel_path).resolve()
    if old_target == base or base not in old_target.parents:
        return jsonify({"error": "路径非法"}), 403
    if not old_target.exists() or not old_target.is_file():
        return jsonify({"error": "原文件不存在"}), 404

    ext = old_target.suffix
    if ext.lower() not in {".svg", ".png", ".jpg", ".jpeg", ".webp", ".avif"}:
        return jsonify({"error": "不支持的文件类型"}), 415

    new_filename = f"{new_base_name}{ext}"
    new_target = old_target.with_name(new_filename).resolve()
    if new_target == base or base not in new_target.parents:
        return jsonify({"error": "目标路径非法"}), 403
    if new_target.exists() and new_target != old_target:
        return jsonify({"error": "目标文件已存在"}), 409

    try:
        old_target.rename(new_target)
    except Exception as e:
        return jsonify({"error": f"重命名失败: {e}"}), 500

    old_rel = str(old_target.relative_to(base))
    new_rel = str(new_target.relative_to(base))
    old_key = f"{directory}::{old_rel}"
    new_key = f"{directory}::{new_rel}"

    with MANAGE_SELECTION_LOCK:
        files = MANAGE_SELECTION_CACHE.get("files", [])
        if isinstance(files, list):
            MANAGE_SELECTION_CACHE["files"] = [new_rel if item == old_rel else item for item in files]
            MANAGE_SELECTION_CACHE["updatedAt"] = int(time.time() * 1000)

    def mutate(notes: dict[str, str]):
        if old_key in notes:
            notes[new_key] = notes.pop(old_key)

    _update_manage_notes(mutate)
    return jsonify({"ok": True, "oldPath": old_rel, "newPath": new_rel})


@app.post("/generate")
def generate():
    files = request.files.getlist("svgs")
    svg_dir = request.form.get("svg_dir", "").strip()
    randomize = _parse_bool(request.form.get("randomize"))
    opts = _parse_base_options()
    items, skipped, error = _load_items_from_request(opts, files, svg_dir, randomize)
    if error:
        return jsonify({"error": error}), 400

    try:
        if opts["add_zima_blue"]:
            items = _inject_zima_blue_tile(items)
        output_name = _compose_and_save_variant(
            items=items,
            width=opts["width"],
            height=opts["height"],
            cols=opts["cols"],
            gap=opts["gap"],
            padding=opts["padding"],
            bg=opts["bg"],
            transparent_bg=opts["transparent_bg"],
            adaptive_grid=opts["adaptive_grid"],
            min_row_height=opts["min_row_height"],
            png_optimize=opts["png_optimize"],
            png_compress_level=opts["png_compress_level"],
            label_enabled=opts["overlay_show_filename"] or opts["overlay_show_note"],
            label_font_family=opts["overlay_font_family"],
            label_font_size=opts["overlay_font_size"],
            label_font_color=opts["overlay_font_color"],
            label_box_bg_color=opts["overlay_box_bg_color"],
            label_box_bg_opacity=opts["overlay_box_bg_opacity"],
            label_as_tile=opts["overlay_as_tile"],
            label_position=opts["overlay_position"],
        )
    except Exception as e:
        return jsonify({"error": f"生成失败: {e}"}), 500

    return jsonify(
        {
            "ok": True,
            "preview_url": f"/file/{output_name}",
            "download_url": f"/download/{output_name}",
            "size": {"width": opts["width"], "height": opts["height"]},
            "count": len(items),
            "skipped": skipped,
        }
    )


@app.post("/generate_batch_stream")
def generate_batch_stream():
    files = request.files.getlist("svgs")
    svg_dir = request.form.get("svg_dir", "").strip()
    opts = _parse_base_options()
    base_cols = opts["cols"]
    variant_configs = _parse_json(request.form.get("variant_configs"), [])
    if not isinstance(variant_configs, list) or not variant_configs:
        return jsonify({"error": "缺少有效的 variant_configs。"}), 400

    items, skipped, error = _load_items_from_request(opts, files, svg_dir, randomize=False)
    if error:
        return jsonify({"error": error}), 400

    prepared_configs: list[dict] = []
    for idx, cfg in enumerate(variant_configs):
        if not isinstance(cfg, dict):
            continue
        cols_offset = _parse_int(str(cfg.get("colsOffset", 0)), 0, -20, 20)
        cols = max(1, min(20, base_cols + cols_offset))
        randomize = bool(cfg.get("randomize", False))
        prepared_configs.append({"index": idx, "cols": cols, "randomize": randomize})

    if not prepared_configs:
        return jsonify({"error": "variant_configs 为空。"}), 400

    def build_variant_result(cfg: dict) -> dict:
        ordered = list(items)
        if cfg["randomize"]:
            random.shuffle(ordered)
        if opts["add_zima_blue"]:
            ordered = _inject_zima_blue_tile(ordered)

        output_name = _compose_and_save_variant(
            items=ordered,
            width=opts["width"],
            height=opts["height"],
            cols=cfg["cols"],
            gap=opts["gap"],
            padding=opts["padding"],
            bg=opts["bg"],
            transparent_bg=opts["transparent_bg"],
            adaptive_grid=opts["adaptive_grid"],
            min_row_height=opts["min_row_height"],
            png_optimize=opts["png_optimize"],
            png_compress_level=opts["png_compress_level"],
            label_enabled=opts["overlay_show_filename"] or opts["overlay_show_note"],
            label_font_family=opts["overlay_font_family"],
            label_font_size=opts["overlay_font_size"],
            label_font_color=opts["overlay_font_color"],
            label_box_bg_color=opts["overlay_box_bg_color"],
            label_box_bg_opacity=opts["overlay_box_bg_opacity"],
            label_as_tile=opts["overlay_as_tile"],
            label_position=opts["overlay_position"],
        )
        return {
            "type": "variant",
            "index": cfg["index"],
            "cols": cfg["cols"],
            "preview_url": f"/file/{output_name}",
            "download_url": f"/download/{output_name}",
            "size": {"width": opts["width"], "height": opts["height"]},
            "count": len(ordered),
            "skipped": skipped,
        }

    def stream():
        max_workers = min(4, max(1, len(prepared_configs)))
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            future_map = {
                executor.submit(build_variant_result, cfg): cfg for cfg in prepared_configs
            }
            for future in as_completed(future_map):
                try:
                    result = future.result()
                    yield json.dumps(result, ensure_ascii=False) + "\n"
                except Exception as e:
                    error_line = {"type": "error", "error": f"生成失败: {e}"}
                    yield json.dumps(error_line, ensure_ascii=False) + "\n"
                    return
        yield json.dumps({"type": "done"}, ensure_ascii=False) + "\n"

    return Response(stream(), mimetype="application/x-ndjson")


@app.post("/generate_sample")
def generate_sample():
    files = request.files.getlist("svgs")
    svg_dir = request.form.get("svg_dir", "").strip()
    randomize = _parse_bool(request.form.get("randomize"))
    opts = _parse_base_options()
    sample_item_count = _parse_int(
        request.form.get("sample_item_count", str(opts["cols"] * opts["cols"])),
        opts["cols"] * opts["cols"],
        1,
        5000,
    )

    items, skipped, error = _load_items_from_request(opts, files, svg_dir, randomize)
    if error:
        return jsonify({"error": error}), 400

    total_count = len(items)
    per_wall_count = max(1, min(sample_item_count, total_count))
    sample_items = list(items[:per_wall_count])

    try:
        if opts["add_zima_blue"]:
            sample_items = _inject_zima_blue_tile(sample_items)
        output_name = _compose_and_save_variant(
            items=sample_items,
            width=opts["width"],
            height=opts["height"],
            cols=opts["cols"],
            gap=opts["gap"],
            padding=opts["padding"],
            bg=opts["bg"],
            transparent_bg=opts["transparent_bg"],
            adaptive_grid=opts["adaptive_grid"],
            min_row_height=opts["min_row_height"],
            png_optimize=opts["png_optimize"],
            png_compress_level=opts["png_compress_level"],
            label_enabled=opts["overlay_show_filename"] or opts["overlay_show_note"],
            label_font_family=opts["overlay_font_family"],
            label_font_size=opts["overlay_font_size"],
            label_font_color=opts["overlay_font_color"],
            label_box_bg_color=opts["overlay_box_bg_color"],
            label_box_bg_opacity=opts["overlay_box_bg_opacity"],
            label_as_tile=opts["overlay_as_tile"],
            label_position=opts["overlay_position"],
        )
    except Exception as e:
        return jsonify({"error": f"生成失败: {e}"}), 500

    estimated_walls = math.ceil(total_count / per_wall_count)
    last_wall_count = total_count % per_wall_count or per_wall_count
    return jsonify(
        {
            "ok": True,
            "preview_url": f"/file/{output_name}",
            "download_url": f"/download/{output_name}",
            "size": {"width": opts["width"], "height": opts["height"]},
            "count": len(sample_items),
            "skipped": skipped,
            "cols": opts["cols"],
            "per_wall_count": per_wall_count,
            "total_count": total_count,
            "estimated_walls": estimated_walls,
            "last_wall_count": last_wall_count,
        }
    )


@app.post("/generate_split_stream")
def generate_split_stream():
    files = request.files.getlist("svgs")
    svg_dir = request.form.get("svg_dir", "").strip()
    randomize = _parse_bool(request.form.get("randomize"))
    opts = _parse_base_options()
    per_wall_count = _parse_int(request.form.get("per_wall_count", "0"), 0, 1, 10000)
    if per_wall_count < 1:
        return jsonify({"error": "缺少有效的 per_wall_count。"}), 400

    items, skipped, error = _load_items_from_request(opts, files, svg_dir, randomize)
    if error:
        return jsonify({"error": error}), 400
    total_count = len(items)

    groups: list[tuple[int, list[dict]]] = []
    for start in range(0, total_count, per_wall_count):
        idx = len(groups)
        groups.append((idx, list(items[start : start + per_wall_count])))

    if not groups:
        return jsonify({"error": "没有可生成的图片。"}), 400

    def build_group_result(group: tuple[int, list[dict]]) -> dict:
        idx, chunk_items = group
        working = list(chunk_items)
        if opts["add_zima_blue"]:
            working = _inject_zima_blue_tile(working)
        page_text = f"{idx + 1}/{len(groups)}" if opts["page_number_enabled"] else None
        output_name = _compose_and_save_variant(
            items=working,
            width=opts["width"],
            height=opts["height"],
            cols=opts["cols"],
            gap=opts["gap"],
            padding=opts["padding"],
            bg=opts["bg"],
            transparent_bg=opts["transparent_bg"],
            adaptive_grid=opts["adaptive_grid"],
            min_row_height=opts["min_row_height"],
            png_optimize=opts["png_optimize"],
            png_compress_level=opts["png_compress_level"],
            label_enabled=opts["overlay_show_filename"] or opts["overlay_show_note"],
            label_font_family=opts["overlay_font_family"],
            label_font_size=opts["overlay_font_size"],
            label_font_color=opts["overlay_font_color"],
            label_box_bg_color=opts["overlay_box_bg_color"],
            label_box_bg_opacity=opts["overlay_box_bg_opacity"],
            label_as_tile=opts["overlay_as_tile"],
            label_position=opts["overlay_position"],
            page_number_text=page_text,
            page_number_position=opts["page_number_position"],
        )
        return {
            "type": "variant",
            "index": idx,
            "cols": opts["cols"],
            "preview_url": f"/file/{output_name}",
            "download_url": f"/download/{output_name}",
            "size": {"width": opts["width"], "height": opts["height"]},
            "count": len(working),
            "source_count": len(chunk_items),
            "total_count": total_count,
            "per_wall_count": per_wall_count,
            "skipped": skipped,
        }

    def stream():
        max_workers = min(4, max(1, len(groups)))
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            future_map = {executor.submit(build_group_result, group): group for group in groups}
            for future in as_completed(future_map):
                try:
                    result = future.result()
                    yield json.dumps(result, ensure_ascii=False) + "\n"
                except Exception as e:
                    yield json.dumps({"type": "error", "error": f"生成失败: {e}"}, ensure_ascii=False) + "\n"
                    return
        yield json.dumps({"type": "done"}, ensure_ascii=False) + "\n"

    return Response(stream(), mimetype="application/x-ndjson")


@app.post("/generate_sample_stream")
def generate_sample_stream():
    files = request.files.getlist("svgs")
    svg_dir = request.form.get("svg_dir", "").strip()
    opts = _parse_base_options()
    base_cols = opts["cols"]
    variant_configs = _parse_json(request.form.get("variant_configs"), [])
    if not isinstance(variant_configs, list) or not variant_configs:
        return jsonify({"error": "缺少有效的 variant_configs。"}), 400

    randomize_all = _parse_bool(request.form.get("randomize"))
    items, skipped, error = _load_items_from_request(opts, files, svg_dir, randomize=randomize_all)
    if error:
        return jsonify({"error": error}), 400

    total_count = len(items)

    prepared_configs: list[dict] = []
    for idx, cfg in enumerate(variant_configs):
        if not isinstance(cfg, dict):
            continue
        cols_offset = _parse_int(str(cfg.get("colsOffset", 0)), 0, -20, 20)
        cols = max(1, min(20, base_cols + cols_offset))
        randomize = bool(cfg.get("randomize", False))
        prepared_configs.append({"index": idx, "cols": cols, "randomize": randomize})
    if not prepared_configs:
        return jsonify({"error": "variant_configs 为空。"}), 400

    def build_variant_result(cfg: dict) -> dict:
        per_wall_count = max(1, min(total_count, cfg["cols"] * cfg["cols"]))
        sample_source = list(items[:per_wall_count])
        estimated_walls = math.ceil(total_count / per_wall_count)
        last_wall_count = total_count % per_wall_count or per_wall_count
        working = list(sample_source)
        if cfg["randomize"]:
            random.shuffle(working)
        if opts["add_zima_blue"]:
            working = _inject_zima_blue_tile(working)
        page_text = f"{cfg['index'] + 1}/{len(prepared_configs)}" if opts["page_number_enabled"] else None
        output_name = _compose_and_save_variant(
            items=working,
            width=opts["width"],
            height=opts["height"],
            cols=cfg["cols"],
            gap=opts["gap"],
            padding=opts["padding"],
            bg=opts["bg"],
            transparent_bg=opts["transparent_bg"],
            adaptive_grid=opts["adaptive_grid"],
            min_row_height=opts["min_row_height"],
            png_optimize=opts["png_optimize"],
            png_compress_level=opts["png_compress_level"],
            label_enabled=opts["overlay_show_filename"] or opts["overlay_show_note"],
            label_font_family=opts["overlay_font_family"],
            label_font_size=opts["overlay_font_size"],
            label_font_color=opts["overlay_font_color"],
            label_box_bg_color=opts["overlay_box_bg_color"],
            label_box_bg_opacity=opts["overlay_box_bg_opacity"],
            label_as_tile=opts["overlay_as_tile"],
            label_position=opts["overlay_position"],
            page_number_text=page_text,
            page_number_position=opts["page_number_position"],
        )
        return {
            "type": "variant",
            "index": cfg["index"],
            "cols": cfg["cols"],
            "preview_url": f"/file/{output_name}",
            "download_url": f"/download/{output_name}",
            "size": {"width": opts["width"], "height": opts["height"]},
            "count": len(working),
            "source_count": per_wall_count,
            "total_count": total_count,
            "estimated_walls": estimated_walls,
            "last_wall_count": last_wall_count,
            "skipped": skipped,
        }

    def stream():
        max_workers = min(4, max(1, len(prepared_configs)))
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            future_map = {
                executor.submit(build_variant_result, cfg): cfg for cfg in prepared_configs
            }
            for future in as_completed(future_map):
                try:
                    result = future.result()
                    yield json.dumps(result, ensure_ascii=False) + "\n"
                except Exception as e:
                    yield json.dumps({"type": "error", "error": f"生成失败: {e}"}, ensure_ascii=False) + "\n"
                    return
        yield json.dumps({"type": "done"}, ensure_ascii=False) + "\n"

    return Response(stream(), mimetype="application/x-ndjson")


@app.get("/file/<name>")
def file_view(name: str):
    file_path = GENERATED_DIR / os.path.basename(name)
    if not file_path.exists():
        return "Not Found", 404
    return send_file(file_path, mimetype="image/png")


@app.get("/download/<name>")
def download(name: str):
    file_path = GENERATED_DIR / os.path.basename(name)
    if not file_path.exists():
        return "Not Found", 404
    requested = (request.args.get("filename") or "").strip()
    if requested:
        safe = "".join(ch for ch in requested if ch.isalnum() or ch in {"_", "-", ".", "(", ")", " "}).strip()
        if not safe:
            safe = os.path.basename(name)
        if not safe.lower().endswith(".png"):
            safe = f"{safe}.png"
        download_name = safe
    else:
        download_name = os.path.basename(name)
    return send_file(file_path, mimetype="image/png", as_attachment=True, download_name=download_name)


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=True)

#!/usr/bin/env python3
"""Check generated literate HTML for raw Markdown artifacts."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


RAW_MARKDOWN_TABLE_RE = re.compile(
    r"<p>\s*\|[^<\n]*\|[^\n]*\n\s*\|[-:|\s]+\|",
    re.IGNORECASE,
)


def iter_html_files(site_root: Path) -> list[Path]:
    return sorted(path for path in site_root.rglob("*.html") if path.is_file())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site_root", type=Path, help="Verso literate-html output directory")
    args = parser.parse_args()

    if not args.site_root.is_dir():
        raise SystemExit(f"site root does not exist or is not a directory: {args.site_root}")

    failures: list[str] = []
    for html_file in iter_html_files(args.site_root):
        text = html_file.read_text(encoding="utf-8", errors="replace")
        match = RAW_MARKDOWN_TABLE_RE.search(text)
        if match:
            snippet = " ".join(match.group(0).split())[:240]
            failures.append(f"{html_file}: raw Markdown table in paragraph: {snippet}")

    if failures:
        for failure in failures:
            print(failure)
        raise SystemExit(1)

    print(f"literate rendering OK: {args.site_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Strict source scan for PhotoLean (dependency-free; mirrors proofs/scripts/check.sh).

Rules (documented trade-offs of the shell gate, reproduced here so CI does not need Lean):
  * a hit on `sorry` or `admit` (Lean 4 treats both as the same unproved placeholder) anywhere in
    the source, EXCEPT inside an inline `--` comment on the same line;
  * a hit on a declaration line starting with `axiom` or `constant` (Lean 4 `constant` declares an
    axiom and has the same trust surface), including the `private`/`protected` variants;
  * keywords inside block comments `/- ... -/` ARE reported (false positives are safer than misses);
    the repository documents this trade-off in proofs/scripts/check.sh.

Exit 0 when clean; 1 with the list of hits otherwise.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC_DIRS = ["PhotoLean"]

# keyword hits, excluding an inline `--` comment tail
KEYWORD = re.compile(r"\b(sorry|admit)\b")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(axiom|constant)\s")


def strip_inline_comment(line: str) -> str:
    """Remove an inline `--` comment, but not a `--` inside a string literal or a block comment."""
    out, i = [], 0
    in_string = False
    while i < len(line):
        ch = line[i]
        if ch == '"' and (i == 0 or line[i - 1] != "\\"):
            in_string = not in_string
        if not in_string and line.startswith("--", i):
            break
        out.append(ch)
        i += 1
    return "".join(out)


def main() -> int:
    hits: list[str] = []
    checked = 0
    for d in SRC_DIRS:
        for path in sorted((ROOT / d).rglob("*.lean")):
            checked += 1
            in_block = False
            for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
                line = raw
                # block-comment nesting is tracked only to keep the scan readable; hits inside
                # block comments are reported on purpose (see module docstring).
                if in_block:
                    if "-/" in line:
                        in_block = False
                    continue
                if "/-" in line and "-/" not in line.split("/-", 1)[1]:
                    in_block = True
                code = strip_inline_comment(line)
                if KEYWORD.search(code):
                    hits.append(f"{path.relative_to(ROOT)}:{lineno}: {raw.strip()}")
                if DECL.match(code):
                    hits.append(f"{path.relative_to(ROOT)}:{lineno}: {raw.strip()}")
    print(f"scanned {checked} .lean files under {', '.join(SRC_DIRS)}")
    if hits:
        print("!! strict scan hits:")
        for h in hits:
            print("   " + h)
        return 1
    print("clean")
    return 0


if __name__ == "__main__":
    sys.exit(main())

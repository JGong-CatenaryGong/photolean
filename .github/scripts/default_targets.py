#!/usr/bin/env python3
"""Check that `lakefile.toml`'s `defaultTargets` equals the set of .lean files on disk.

Why this matters (measured 2026-09-24, see review/REVIEW-PROMPT.md §10.3): the bare gate
`proofs/scripts/check.sh --strict` runs `lake build` with no arguments, which builds exactly
`defaultTargets`. A module that exists on disk but is absent from that list is therefore never
compiled by the gate — a delivered file could fail to compile while the gate still reports PASS.

Exit 0 when the two sets agree; 1 otherwise.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]


def disk_modules() -> set[str]:
    return {
        ".".join(p.relative_to(ROOT).with_suffix("").parts)
        for p in (ROOT / "PhotoLean").rglob("*.lean")
    }


def declared_targets() -> set[str]:
    text = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    block = text.split("defaultTargets", 1)[1].split("]", 1)[0]
    return set(re.findall(r'"(PhotoLean[^"]+)"', block))


def main() -> int:
    disk, targets = disk_modules(), declared_targets()
    missing = sorted(disk - targets)
    extra = sorted(targets - disk)
    print(f"defaultTargets: {len(targets)} | on disk: {len(disk)}")
    if missing:
        print("!! on disk but NOT built by the bare gate:")
        for m in missing:
            print("   " + m)
    if extra:
        print("!! declared as a target but not on disk:")
        for e in extra:
            print("   " + e)
    if missing or extra:
        return 1
    print("defaultTargets == disk module set")
    return 0


if __name__ == "__main__":
    sys.exit(main())

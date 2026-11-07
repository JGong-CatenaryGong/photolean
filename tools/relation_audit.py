#!/usr/bin/env python3
"""Thin executable wrapper for the relation-audit validator.

Keeping this file small means ``python3 tools/relation_audit.py`` works from the
repository root while the implementation stays importable as
``tools.relation_audit`` (for tests and embedding).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from relation_audit.cli import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())

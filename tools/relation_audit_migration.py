#!/usr/bin/env python3
"""Thin executable wrapper for the R3 migration-fragment checker.

Keeping this file small means ``python3 tools/relation_audit_migration.py``
works from the repository root while the implementation stays importable as
``tools.relation_audit.migration`` (for tests and embedding).
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from relation_audit.migration import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())

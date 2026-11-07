#!/usr/bin/env python3
"""Run the relation-audit test suite.

    python3 tests/relation_audit/run_tests.py
    python3 -m unittest tests.relation_audit.run_tests   # if run as a module

The suite needs the pinned Lean toolchain for the certificate checks.  If the
toolchain is absent those tests are reported as skipped, never as passed.
"""

from __future__ import annotations

import os
import sys
import unittest


HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def main() -> int:
    loader = unittest.TestLoader()
    suite = loader.discover(HERE, pattern="test_*.py", top_level_dir=HERE)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())

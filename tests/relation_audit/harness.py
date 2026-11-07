"""Shared harness for the relation-audit tests.

The fixture certificates live in a mock Lean module under
``tests/relation_audit/fixtures/lean``.  The harness compiles that module to an
``.olean`` inside the checkout's gitignored ``.lake/tmp`` area and passes the
containing directory as ``--lean-root`` so the validator's generated check file
can import it.  This keeps the fixture independent of the still-in-flight
``PhotoLean/RelationAudit`` modules while exercising the real Lean toolchain.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TOOL = os.path.join(REPO_ROOT, "tools", "relation_audit.py")
FIXTURES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures")
SCHEMA = os.path.join(FIXTURES, "schema.json")
PILOT = os.path.join(FIXTURES, "manifest_pilot.json")
FULL = os.path.join(FIXTURES, "manifest_full.json")
INVALID_DIR = os.path.join(FIXTURES, "invalid")
MOCK_SOURCE = os.path.join(FIXTURES, "lean", "RelationAuditFixture.lean")
LAKE = os.path.join(REPO_ROOT, "proofs", "scripts", "lake")

_mock_cache: dict[str, object] = {"done": False, "root": None, "reason": ""}


def work_dir() -> str:
    """Per-process scratch directory.

    The checkout is shared by concurrent agents and test runs, so the harness
    must not remove or reuse another process's mock module or mutant files.
    """
    path = os.path.join(REPO_ROOT, ".lake", "tmp", "relation-audit-tests",
                        f"run-{os.getpid()}")
    os.makedirs(path, exist_ok=True)
    return path


def toolchain_available() -> bool:
    return os.path.isfile(LAKE) and os.path.isfile(
        os.path.join(REPO_ROOT, ".toolchain", "lean-4.17.0-linux", "bin", "lean"))


def mock_lean_root() -> tuple[str | None, str]:
    """Compile the fixture Lean module once; return (import_root, reason)."""
    if _mock_cache["done"]:
        return _mock_cache["root"], _mock_cache["reason"]  # type: ignore[return-value]
    _mock_cache["done"] = True
    if not toolchain_available():
        _mock_cache["reason"] = "Lean toolchain not available"
        return None, _mock_cache["reason"]  # type: ignore[return-value]
    work = work_dir()
    root = os.path.join(work, "root")
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(root, exist_ok=True)
    source = os.path.join(root, "RelationAuditFixture.lean")
    shutil.copyfile(MOCK_SOURCE, source)
    relative_root = os.path.relpath(root, REPO_ROOT)
    relative_source = os.path.relpath(source, REPO_ROOT)
    command = [LAKE, "env", "lean", f"--root={relative_root}",
               "-o", os.path.join(root, "RelationAuditFixture.olean"),
               relative_source]
    completed = subprocess.run(command, cwd=REPO_ROOT, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if completed.returncode != 0:
        _mock_cache["reason"] = (
            "mock Lean module failed to compile: "
            + (completed.stderr or completed.stdout).strip()[:500])
        return None, _mock_cache["reason"]  # type: ignore[return-value]
    _mock_cache["root"] = root
    return root, ""


def run_cli(manifest: str, mode: str = "pilot", *, schema: str = SCHEMA,
            no_lean: bool = False, lean_root: str | None = None,
            json_out: str | None = None, extra: list[str] | None = None) -> subprocess.CompletedProcess:
    command = [sys.executable, TOOL, "--manifest", manifest, "--schema", schema]
    if mode:
        command.extend(["--mode", mode])
    if no_lean:
        command.append("--no-lean")
    if lean_root:
        command.extend(["--lean-root", lean_root])
    if json_out:
        command.extend(["--json-out", json_out])
    if extra:
        command.extend(extra)
    return subprocess.run(command, cwd=REPO_ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)


def failure_codes(stdout: str) -> set[str]:
    codes = set()
    for line in stdout.splitlines():
        stripped = line.strip()
        if stripped.startswith("FAIL "):
            token = stripped.split()[1]
            codes.add(token.rstrip(":"))
    return codes


def load_json(path: str) -> dict:
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


def write_mutant(data: dict) -> str:
    work = os.path.join(work_dir(), "mutants")
    os.makedirs(work, exist_ok=True)
    handle = tempfile.NamedTemporaryFile(
        mode="w", suffix=".json", dir=work, delete=False, encoding="utf-8")
    json.dump(data, handle)
    handle.close()
    return handle.name


def invalid_fixture(name: str) -> str:
    return os.path.join(INVALID_DIR, name)


def report_from(json_path: str) -> dict:
    return load_json(json_path)

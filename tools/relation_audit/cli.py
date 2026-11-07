#!/usr/bin/env python3
"""Command line entry point for the certified relation audit.

Usage:
    python3 tools/relation_audit.py --manifest relation_audit/pilot.json --mode pilot

Exit codes:
    0  every requested gate ran and passed;
    1  at least one requested check failed;
    2  the run is incomplete (missing contract files), or a requested gate was
       skipped (a skipped Lean check is never PASS), or the input could not be
       loaded.

The validator never edits the schema or the manifest.  The only generated file
is a temporary Lean check module under ``.lake/tmp/relation-audit`` (or the
system temporary directory), removed after the run unless ``--keep-temps`` is
given.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import traceback

from . import json_schema
from .report import PASS, Report
from .validator import AuditValidator, ContractError, load_manifest


def repo_root_from(start: str) -> str:
    current = os.path.abspath(start)
    while True:
        if os.path.isfile(os.path.join(current, "proofs", "ENGINE.yml")):
            return current
        parent = os.path.dirname(current)
        if parent == current:
            return os.path.abspath(start)
        current = parent


def _load_schema(path: str) -> json_schema.Schema:
    try:
        return json_schema.Schema.from_path(path)
    except FileNotFoundError as exc:
        raise ContractError(f"schema not found: {path}") from exc
    except OSError as exc:
        raise ContractError(f"cannot read schema {path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ContractError(f"schema {path} is not valid JSON: {exc}") from exc
    except json_schema.SchemaError as exc:
        raise ContractError(f"schema {path} is not usable: {exc}") from exc


def _render(report: Report, verbose: bool) -> None:
    print(f"== RelationAudit ({report.mode} mode) ==")
    print(f"manifest: {report.manifest}")
    print(f"schema:   {report.schema}")
    for gate in report.gates.values():
        print(f"  {gate.name:<12} {gate.status:<14} "
              f"({len(gate.findings)} checks)")
        for finding in gate.findings:
            if finding.status != PASS or verbose:
                location = f" [{finding.location}]" if finding.location else ""
                print(f"    {finding.status:<4} {finding.code}{location}: {finding.message}")
    coverage = report.coverage
    if coverage:
        print("coverage:")
        print(f"  theories          {coverage.get('theoryCount')}/"
              f"{coverage.get('expectedTheoryCount')}")
        print(f"  registry          {coverage.get('coveredPairs')}/"
              f"{coverage.get('expectedPairUniverse')} pairs")
        print(f"  resolved          {coverage.get('resolvedPairs')}/"
              f"{coverage.get('expectedPairUniverse')} pairs "
              f"(complete={coverage.get('resolvedCoverageComplete')})")
        if coverage.get("missingPairs"):
            missing = coverage["missingPairs"]
            shown = missing[:12]
            suffix = "" if len(missing) <= 12 else f" ... (+{len(missing) - 12} more)"
            print(f"  missing pairs     {shown}{suffix}")
        print(f"  unresolved records {coverage.get('unresolvedRecords')}")
    if report.counts:
        print("counts:")
        print(f"  by status         {report.counts.get('byStatus')}")
        print(f"  certified by kind {report.counts.get('certifiedByKind')}")
    for caveat in report.caveats:
        print(f"caveat: {caveat.get('code')}: {caveat.get('message')}")
    if report.unresolved:
        print("unresolved set:")
        for item in report.unresolved:
            print(f"  {item.get('record')} query={item.get('queryId')} "
                  f"version={item.get('statementVersion')} scope={item.get('scope')}")
    print(f"overall: {report.status} (exit {report.exit_code})")


def build_parser(default_root: str) -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="relation_audit.py",
        description="Fail-closed validator for the PhotoLean certified relation audit.",
        epilog="Exit 0 = PASS; 1 = FAIL; 2 = INCOMPLETE or unloadable input. "
               "A skipped Lean check is never PASS.",
    )
    parser.add_argument("--manifest", default=os.path.join(default_root, "relation_audit", "pilot.json"),
                        help="manifest JSON (default: relation_audit/pilot.json)")
    parser.add_argument("--schema", default=os.path.join(default_root, "relation_audit", "schema.json"),
                        help="contract JSON schema (default: relation_audit/schema.json)")
    parser.add_argument("--repo-root", default=default_root,
                        help="repository root (default: the checkout containing this tool)")
    parser.add_argument("--mode", choices=("full", "pilot"), default=None,
                        help="full requires 136/136 pair coverage; pilot requires the "
                             "seven kinds plus unresolved and notEstablished; defaults to "
                             "the manifest's mode field, then full")
    parser.add_argument("--no-lean", action="store_true",
                        help="do not run Lean checks; if certificates exist the run is "
                             "INCOMPLETE (exit 2), never PASS")
    parser.add_argument("--lean-root", action="append", default=[],
                        help="extra Lean import root (used by fixture tests; repeatable)")
    parser.add_argument("--lean-timeout", type=float, default=300.0,
                        help="Lean check timeout in seconds (default: 300)")
    parser.add_argument("--keep-temps", action="store_true",
                        help="keep the generated Lean file for debugging")
    parser.add_argument("--json-out", default=None,
                        help="write the machine-readable report to this path")
    parser.add_argument("--lean-source-out", default=None,
                        help="archive the generated Lean check file at this path")
    parser.add_argument("--quiet", action="store_true", help="only print the overall verdict")
    parser.add_argument("--verbose", action="store_true", help="print passing checks too")
    return parser


def main(argv: list[str] | None = None) -> int:
    default_root = repo_root_from(os.path.dirname(os.path.abspath(__file__)))
    parser = build_parser(default_root)
    args = parser.parse_args(argv)

    try:
        schema = _load_schema(args.schema)
        manifest = load_manifest(args.manifest)
        manifest_mode = manifest.get("mode")
        mode = args.mode or (manifest_mode if manifest_mode in ("full", "pilot")
                             else "full")
        validator = AuditValidator(
            manifest=manifest,
            schema=schema,
            repo_root=args.repo_root,
            manifest_path=args.manifest,
            schema_path=args.schema,
            mode=mode,
            no_lean=args.no_lean,
            lean_roots=args.lean_root,
            lean_timeout=args.lean_timeout,
            keep_temps=args.keep_temps,
            lean_source_out=args.lean_source_out,
        )
        report = validator.run()
    except ContractError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    except Exception:  # pragma: no cover - defensive fail-closed boundary
        print("ERROR: validator crashed; treating this run as INCOMPLETE", file=sys.stderr)
        traceback.print_exc()
        return 2

    if args.json_out:
        try:
            with open(args.json_out, "w", encoding="utf-8") as handle:
                json.dump(report.to_json(), handle, indent=2, sort_keys=True)
                handle.write("\n")
        except OSError as exc:
            print(f"ERROR: cannot write report {args.json_out}: {exc}", file=sys.stderr)
            return 2

    if args.quiet:
        print(f"{report.status} (exit {report.exit_code})")
    else:
        _render(report, args.verbose)
    return report.exit_code


if __name__ == "__main__":
    sys.exit(main())

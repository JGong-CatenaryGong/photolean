"""Single-source migration inventory and disposition checker (R2).

This module derives every declaration and every unordered theory pair from the
repository census authority, ``tools/counts.py``.  It does not maintain a second
declaration list and it does not maintain a second pair list:

* declarations come from ``counts.all_lean_files`` + ``counts.scan_file`` and the
  section assignment from ``counts.relations_census``;
* pairs come from ``counts.THEORIES`` and the explicit legacy edge/absence sets
  in ``counts.EDGES`` / ``counts.ABSENCE_REGISTRIES`` through
  ``counts.pair_census``.

The generated JSON is a *migration inventory*, not an audit registry and not an
audit verdict.  Legacy ``edge`` / ``absence`` labels keep their historical
meaning only and are namespaced under ``legacy`` with
``nonAuditMetadata = true``.  They are never mapped to the audit statuses
``certified`` / ``unresolved`` / ``notEstablished`` / ``outOfScope``.

Commands (run from the repository root)::

    python3 tools/relation_audit_inventory.py --generate
    python3 tools/relation_audit_inventory.py --check

``--check`` fails closed on scanner drift, count drift, a stale checked-in
artifact, or a disposition ledger that does not cover every scanned declaration
exactly once with a disposition, a rationale, provenance, and valid references.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import sys
from itertools import combinations
from typing import Any

if __package__:
    from . import json_schema
else:  # pragma: no cover - direct script execution fallback
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import json_schema  # type: ignore


SCHEMA_VERSION = "1.0.0"

RELATIONS = "PhotoLean/Relations.lean"
SCANNER = "tools/counts.py"
DISPOSITIONS = "relation_audit/dispositions.json"
DISPOSITIONS_SCHEMA = "relation_audit/dispositions.schema.json"
PILOT = "relation_audit/pilot.json"
GENERATED_DECLARATIONS = "relation_audit/generated/relations_inventory.json"
GENERATED_PAIRS = "relation_audit/generated/pair_inventory.json"
REPORT_JSON = "relation_audit/reports/inventory-report.json"
REPORT_MD = "relation_audit/reports/inventory-report.md"

# Acceptance totals from the R2 round contract and tools/counts.py.  These are
# totals, not declaration or pair lists: the lists are always scanned.
EXPECTED = {
    "declarations": 78,
    "sections": 17,
    "sectionsWithDeclarations": 15,
    "documentationOnlySections": [10, 16],
    "pairs": 136,
    "legacyEdges": 26,
    "legacyUniqueAbsences": 110,
    "legacyCoveredPairs": 136,
    "unaccountedPairs": 0,
    "bothEdgeAndAbsencePairs": 0,
    "duplicateRegistryRows": 4,
    "ambiguousPairs": 1,
    "completionBlockPairs": 26,
}

AUDIT_STATUS_WORDS = frozenset({"certified", "unresolved", "notEstablished", "outOfScope"})
AUDIT_RELATION_KINDS = frozenset(
    {
        "definitionalIdentity",
        "implication",
        "equivalence",
        "conditionalComposition",
        "observationalEquivalence",
        "distinguishability",
        "refutation",
    }
)

DISPOSITION_VOCABULARY = [
    {
        "id": "pilot-certificate",
        "description": (
            "Already represented by an R1 pilot certificate or by a direct parent of one; "
            "reuse the pilot certificate instead of creating a duplicate."
        ),
    },
    {
        "id": "certificate-required",
        "description": (
            "Direct relation row that still needs a typed certificate before it can become "
            "an audit record."
        ),
    },
    {
        "id": "support-lemma",
        "description": (
            "Supporting lemma consumed by a certificate or composition; it is not itself a "
            "standalone relation certificate."
        ),
    },
    {
        "id": "intra-theory-adjudication",
        "description": (
            "Intra-theory adjudication (A1/A2/A3) or its boundary; a legal audit record but "
            "never one of the 136 cross-theory pairs."
        ),
    },
    {
        "id": "look-alike-non-relation",
        "description": (
            "Shape resemblance, non-relation, or contrast; it must not be flattened into a "
            "direct certified edge."
        ),
    },
    {
        "id": "metadata-only",
        "description": (
            "Machine-checkable shape or boundary note used as metadata; it carries no "
            "relation certificate and no edge."
        ),
    },
    {
        "id": "scoped-relation-documentation",
        "description": (
            "Scoped, one-sided, or transitive registration documenting how a theory sits on "
            "the graph; not a direct certificate."
        ),
    },
    {
        "id": "unresolved-candidate",
        "description": (
            "Associated only with an undelivered candidate relation; no certificate exists "
            "and the candidate remains unresolved as a migration item."
        ),
    },
]

RELATION_ROLE_VOCABULARY = [
    {"id": "definitional-pin", "description": "Kernel-to-theory definitional rfl pin."},
    {"id": "definitional-alias", "description": "Two delivered definitions with the same body."},
    {"id": "direct-equivalence", "description": "Non-definitional cross-theory equivalence."},
    {"id": "one-way-entailment", "description": "Cross-theory implication in one direction only."},
    {"id": "conditional-equivalence", "description": "Equivalence under an explicit modelling premise."},
    {"id": "composition", "description": "Delivered composition or composition-shaped identity."},
    {"id": "composition-component", "description": "Intermediate lemma consumed by a composition."},
    {"id": "model-level-composition", "description": "Composition stated at the modelling level, not by a typed parent."},
    {"id": "support", "description": "Supporting fact with no direct relational content."},
    {"id": "intra-theory-bridge", "description": "Bridge between two readings inside one theory."},
    {"id": "intra-theory-adjudication", "description": "Adjudication whose endpoints are one theory."},
    {"id": "adjudication-verdict", "description": "Verdict row of an A1/A2/A3 adjudication."},
    {"id": "adjudication-boundary", "description": "Boundary or observable row of an adjudication."},
    {"id": "look-alike-shared-form", "description": "Shared functional form or predicate, not an edge."},
    {"id": "look-alike-contrast", "description": "Checkable difference that separates a look-alike."},
    {"id": "shape-note", "description": "Machine note about a shape or boundary, not an edge."},
    {"id": "one-sided-note", "description": "Machine note that pins only one side of a pair."},
    {"id": "transitive-tie-back", "description": "Tie-back certificate whose pair reading is transitive."},
]

# Pair-level migration annotations.  Keys are unordered theory pairs, so the
# canonical pair ID is computed at generation time rather than hand-written.
# Only exceptional readings are listed; every other pair keeps the default
# `direct-edge` or `registered-absence` subtype.
PAIR_ANNOTATIONS: dict[frozenset[str], dict[str, str]] = {
    frozenset(("Marcus", "Hammond")): {
        "subtype": "direct",
        "note": "Direct equivalences, definitional aliases, and the exactness contrast.",
    },
    frozenset(("Marcus", "BEP")): {
        "subtype": "direct",
        "note": "Definitional aliases plus one-way entailments and the headline equivalence.",
    },
    frozenset(("Hammond", "BEP")): {
        "subtype": "direct",
        "note": "Equivalences and one-way entailments; includes the exactness contrast.",
    },
    frozenset(("Marcus", "Kasha")): {
        "subtype": "conditional-premise",
        "note": "Conditional equivalence under the declared hic modelling premise.",
    },
    frozenset(("BEP", "Sabatier")): {
        "subtype": "composition",
        "note": "Sabatier-to-BEP composition rows; each is a candidate typed composition.",
    },
    frozenset(("Marcus", "Sabatier")): {
        "subtype": "look-alike",
        "note": (
            "Look-alike pair: one shared functional form and one shared predicate, "
            "then three non-relations. Not a direct edge."
        ),
    },
    frozenset(("Marcus", "SymmetryFactor")): {
        "subtype": "transitive-via-kernel",
        "note": "A1 tie-back to the shared kernel; no row names Marcus directly.",
    },
    frozenset(("BEP", "SymmetryFactor")): {
        "subtype": "transitive-via-kernel",
        "note": "A1 tie-back to BEP.transfer through the kernel/E1 chain.",
    },
    frozenset(("Hammond", "SymmetryFactor")): {
        "subtype": "transitive-registry-only",
        "note": (
            "No direct row names both theories; the legacy edge rests on the section-10 "
            "registry line and the section-1 kernel certificates."
        ),
    },
    frozenset(("Kasha", "KashaVavilov")): {
        "subtype": "adjudication",
        "note": "A2 adjudication of Kasha's rule against Vavilov behavior; intra-theory reading.",
    },
    frozenset(("Marcus", "EnergyGapLaw")): {
        "subtype": "definitional",
        "note": "EnergyGapLaw rate and inverted-gap predicate pinned to Marcus.",
    },
    frozenset(("Marcus", "ICvsISC")): {
        "subtype": "definitional",
        "note": "ICvsISC internal-conversion rate pinned to the Marcus rate.",
    },
    frozenset(("Kasha", "QuantumYield")): {
        "subtype": "composition",
        "note": "Ladder radiative branch as a two-channel quantum yield.",
    },
    frozenset(("SternVolmer", "QuantumYield")): {
        "subtype": "composition",
        "note": "Dynamic quenching as quantum-yield dilution.",
    },
    frozenset(("QuantumYield", "FluorPhos")): {
        "subtype": "composition",
        "note": "Fluorescence and phosphorescence yields as quantum-yield compositions.",
    },
    frozenset(("QuantumYield", "Einstein")): {
        "subtype": "composition",
        "note": "Einstein radiative channel anchored to the quantum-yield layer.",
    },
    frozenset(("QuantumYield", "Forster")): {
        "subtype": "composition",
        "note": "FRET efficiency as one minus the donor yield.",
    },
    frozenset(("Kasha", "EnergyGapLaw")): {
        "subtype": "one-sided",
        "note": (
            "The legacy edge cites marcusIC_strictAnti_on_inverted_gaps, which does not "
            "consume any EnergyGapLaw declaration."
        ),
    },
    frozenset(("EnergyGapLaw", "StokesShift")): {
        "subtype": "predicate-equivalence",
        "note": "EGL barrier zero iff the Stokes emission window closes.",
    },
    frozenset(("EnergyGapLaw", "ICvsISC")): {
        "subtype": "definitional",
        "note": "ICvsISC rate equals the EnergyGapLaw nonradiative rate.",
    },
    frozenset(("SternVolmer", "FluorPhos")): {
        "subtype": "model-level-composition",
        "note": (
            "The quench is encoded as the added rate kq*q, not through a SternVolmer "
            "declaration; a typed certificate needs an explicit translation."
        ),
    },
    frozenset(("Hammond", "EnergyGapLaw")): {
        "subtype": "shape",
        "note": (
            "The legacy edge cites the boundary row eg_boundary_eq_tsCoord_zero, a kernel "
            "identity rather than a direct EGL-Hammond relation."
        ),
    },
    frozenset(("Marcus", "StokesShift")): {
        "subtype": "in-module",
        "note": "The edge is delivered inside StokesShift.Criterion (row SS-C9), not re-exported here.",
    },
    frozenset(("QuantumYield", "RACI")): {
        "subtype": "composition",
        "note": "RACI quantum yield as a two-channel quantum yield.",
    },
    frozenset(("EnergyGapLaw", "RACI")): {
        "subtype": "one-sided",
        "note": "log_barrierRate_eq pins the RACI affine log shape and consumes no EnergyGapLaw row.",
    },
    frozenset(("ICvsISC", "RACI")): {
        "subtype": "one-sided",
        "note": "icvsisc_barrier_zero_at_crossing pins the ICvsISC side only.",
    },
    frozenset(("KashaVavilov", "EnergyGapLaw")): {
        "subtype": "undelivered-candidate",
        "reason": (
            "Section 16 completion block: EnergyGapLaw against KashaVavilov is registered as "
            "a no-edge pair, and the EnergyGapLaw bullet calls KashaVavilov an undelivered "
            "composition candidate."
        ),
    },
    frozenset(("Kasha", "SternVolmer")): {
        "subtype": "undelivered-candidate",
        "reason": (
            "Section 16: 'Kasha against SternVolmer - no edge (registered candidate, not "
            "delivered)'."
        ),
    },
    frozenset(("KashaVavilov", "SternVolmer")): {
        "subtype": "undelivered-candidate",
        "reason": (
            "Section 16: 'KashaVavilov against SternVolmer / QuantumYield - undelivered "
            "candidate compositions'."
        ),
    },
    frozenset(("KashaVavilov", "QuantumYield")): {
        "subtype": "undelivered-candidate",
        "reason": (
            "Section 16: 'KashaVavilov against SternVolmer / QuantumYield - undelivered "
            "candidate compositions'."
        ),
    },
    frozenset(("Kasha", "FluorPhos")): {
        "subtype": "undelivered-candidate",
        "reason": (
            "Section 16: 'FluorPhos against Kasha / KashaVavilov - no edge (undelivered "
            "candidate compositions)'."
        ),
    },
    frozenset(("KashaVavilov", "FluorPhos")): {
        "subtype": "undelivered-candidate",
        "reason": (
            "Section 16: 'FluorPhos against Kasha / KashaVavilov - no edge (undelivered "
            "candidate compositions)'."
        ),
    },
    frozenset(("SternVolmer", "Forster")): {
        "subtype": "look-alike",
        "note": (
            "Section 16 Forster bullet: the SV look-alike fretEff6_inv_eq_one_plus is a "
            "registered shape with machine content; no edge."
        ),
    },
    frozenset(("Goldschmidt", "Forster")): {
        "subtype": "look-alike",
        "note": "Section 16 completion: Forster against Goldschmidt - no edge (look-alike, no machine row).",
    },
    frozenset(("Sabatier", "Goldschmidt")): {
        "subtype": "look-alike",
        "note": "Section 10: a look-alike of shape, with no edge.",
    },
    frozenset(("Marcus", "RACI")): {
        "subtype": "look-alike",
        "note": (
            "Section 17 row kernel_surfaces_cross_at_tsCoord is a look-alike machine note; "
            "the pair is counted as a legacy absence and carries the census ambiguity note."
        ),
    },
    frozenset(("BEP", "EnergyGapLaw")): {
        "subtype": "shape",
        "note": "Section 16 completion: EnergyGapLaw against BEP - no edge (a registered shape edge).",
    },
    frozenset(("FluorPhos", "ICvsISC")): {
        "subtype": "premise-level",
        "note": "Section 16: the premise-level kISC identification is registered as a modelling premise, not a Lean row.",
    },
}


class InventoryError(Exception):
    """A hard inventory build failure (the generator must not write artifacts)."""


class Finding:
    """One fail-closed inventory finding."""

    def __init__(self, code: str, message: str, location: str | None = None):
        self.code = code
        self.message = message
        self.location = location

    def __str__(self) -> str:
        suffix = f" [{self.location}]" if self.location else ""
        return f"FAIL {self.code}{suffix}: {self.message}"

    def as_dict(self) -> dict[str, Any]:
        return {"code": self.code, "message": self.message, "location": self.location}


# --------------------------------------------------------------------------- paths


def repo_root(start: str | None = None) -> str:
    """Walk up to the checkout holding ``proofs/ENGINE.yml``."""
    current = os.path.abspath(start or os.path.dirname(os.path.abspath(__file__)))
    if os.path.isfile(current):
        current = os.path.dirname(current)
    while True:
        if os.path.isfile(os.path.join(current, "proofs", "ENGINE.yml")):
            return current
        parent = os.path.dirname(current)
        if parent == current:
            raise InventoryError(f"cannot locate repository root above {start!r}")
        current = parent


def _path(root: str, relative: str) -> str:
    return os.path.join(root, relative)


def sha256_file(path: str) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_json(path: str) -> Any:
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


def json_text(value: Any) -> str:
    """Canonical deterministic JSON text."""
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def load_counts_module(root: str):
    """Load ``tools/counts.py`` as an isolated module (no second list)."""
    path = _path(root, SCANNER)
    spec = importlib.util.spec_from_file_location("photolean_counts", path)
    if spec is None or spec.loader is None:  # pragma: no cover - defensive
        raise InventoryError(f"cannot load scanner {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# ------------------------------------------------------------------------ scanning


def scan_repository(root: str, counts_module=None):
    """Return (files, relation_rows, relations_census, pair_census) from counts.py."""
    counts = counts_module or load_counts_module(root)
    files = counts.all_lean_files()
    declarations = []
    for relative in files:
        declarations.extend(counts.scan_file(relative))
    relations = counts.relations_census(declarations)
    pairs = counts.pair_census()
    rows = [row for row in declarations if row.path == counts.RELATIONS]
    return files, rows, relations, pairs


def _section_number(row) -> int:
    value = getattr(row, "section", None)
    if value is None:
        raise InventoryError(f"declaration {row.name!r} has no section assignment")
    return int(value)


def build_declaration_inventory(root: str, counts_module=None) -> dict[str, Any]:
    """Build the 78-declaration inventory from the counts.py scanner only."""
    counts = counts_module or load_counts_module(root)
    _, rows, relations, _ = scan_repository(root, counts)
    section_by_number = {section["number"]: section for section in relations["sections"]}
    seen_ids: set[str] = set()
    entries = []
    for row in sorted(rows, key=lambda item: item.line):
        section = _section_number(row)
        name = row.name or ""
        if not name:
            raise InventoryError(f"anonymous declaration at {row.path}:{row.line}")
        declaration_id = f"D-S{section:02d}-{name}"
        if declaration_id in seen_ids:
            raise InventoryError(f"duplicate stable declaration id {declaration_id}")
        seen_ids.add(declaration_id)
        section_info = section_by_number.get(section)
        if section_info is None:
            raise InventoryError(f"declaration {name!r} refers to unknown section {section}")
        legacy_class = (
            counts.CLASS_OF_ROW.get(name)
            or counts.CLASS_OF_SECTION.get(str(section))
            or "other"
        )
        entries.append(
            {
                "declarationId": declaration_id,
                "name": name,
                "qualifiedName": row.fqname,
                "kind": row.kind,
                "section": section,
                "sectionTitle": section_info["title"],
                "sourceLocator": {
                    "artifact": row.path,
                    "section": section,
                    "line": row.line,
                },
                "legacy": {
                    "class": legacy_class,
                    "sectionClass": counts.CLASS_OF_SECTION.get(str(section)),
                    "rflCertificateSection": str(section) in counts.RFL_CERTIFICATE_SECTIONS,
                    "nonAuditMetadata": True,
                    "note": (
                        "Legacy Fig. 3/section class from tools/counts.py. It is not an "
                        "audit relation kind and not an audit status."
                    ),
                },
            }
        )

    sections = []
    for section in relations["sections"]:
        sections.append(
            {
                "id": f"S{section['number']:02d}",
                "number": section["number"],
                "title": section["title"],
                "line": section["line"],
                "endLine": section["end_line"],
                "declarationCount": section["rows"],
                "declarationIds": [
                    f"D-S{section['number']:02d}-{name}" for name in section["row_names"]
                ],
                "rowNames": list(section["row_names"]),
                "legacyClass": section["class"],
                "documentationOnly": section["rows"] == 0,
            }
        )

    documentation_only = sorted(
        section["number"] for section in relations["sections"] if section["rows"] == 0
    )
    artifact = {
        "schemaVersion": SCHEMA_VERSION,
        "artifactKind": "relation-declaration-inventory",
        "scope": "migration-inventory-only",
        "source": {
            "scanner": SCANNER,
            "scannerSha256": sha256_file(_path(root, SCANNER)),
            "relations": RELATIONS,
            "relationsSha256": sha256_file(_path(root, RELATIONS)),
            "enumeration": [
                "tools/counts.py:all_lean_files",
                "tools/counts.py:scan_file",
                "tools/counts.py:relations_census",
            ],
            "nonAuditMetadata": True,
        },
        "counts": {
            "declarations": len(entries),
            "sections": relations["section_count"],
            "sectionsWithDeclarations": relations["section_count"] - len(documentation_only),
            "documentationOnlySections": documentation_only,
            "rflCertificateRows": relations["rfl_certificate_count"],
            "legacyClassTotals": relations["class_totals"],
            "legacyQuotedClassTotals": relations["quoted_class_totals"],
            "legacyClassVerdicts": relations["class_verdicts"],
            "legacyClassTotalsSum": relations["class_totals_sum"],
        },
        "sections": sections,
        "declarations": entries,
        "nonClaims": [
            "This is a source inventory, not an audit registry.",
            "Legacy section/class labels are not audit relation kinds or audit statuses.",
            "No declaration is certified, resolved, or migrated by appearing here.",
        ],
    }
    return artifact


def _pair_id(first: str, second: str, order: dict[str, int]) -> tuple[str, list[str]]:
    if order[first] <= order[second]:
        return f"P-{first}-{second}", [first, second]
    return f"P-{second}-{first}", [second, first]


def build_pair_inventory(root: str, counts_module=None) -> dict[str, Any]:
    """Build all C(17,2) pairs from counts.py pair census data."""
    counts = counts_module or load_counts_module(root)
    _, _, _, census = scan_repository(root, counts)
    theories = list(counts.THEORIES)
    if len(theories) != 17 or len(set(theories)) != 17:
        raise InventoryError("counts.THEORIES is not a 17-theory inventory")
    order = {theory: index for index, theory in enumerate(theories)}

    edge_map = {frozenset(row["pair"]): row for row in census["edges"]}
    absence_map = {frozenset(row["pair"]): row for row in census["absences"]}
    double_map: dict[frozenset[str], list[str]] = {}
    for row in census["registry_double_listings"]:
        double_map.setdefault(frozenset(row["pair"]), []).extend(row["registries"])
    ambiguous_map = {frozenset(row["pair"]): row for row in census["ambiguous_pairs"]}

    pairs = []
    unaccounted: list[dict[str, Any]] = []
    for first, second in combinations(theories, 2):
        key = frozenset((first, second))
        pair_id, ordered = _pair_id(first, second, order)
        annotation = PAIR_ANNOTATIONS.get(key, {})
        if key in edge_map:
            row = edge_map[key]
            label = "edge"
            registry = "EDGES"
            citation = row["cite"]
            also_listed = double_map.get(key, [])
        elif key in absence_map:
            row = absence_map[key]
            label = "absence"
            registry = row["registry"]
            citation = row["cite"]
            also_listed = double_map.get(key, [])
        else:
            label = "unaccounted"
            registry = None
            citation = None
            also_listed = []
            unaccounted.append({"pairId": pair_id, "theories": ordered})
        subtype = annotation.get("subtype") or (
            "direct-edge" if label == "edge" else "registered-absence"
        )
        ambiguous = ambiguous_map.get(key)
        candidate = None
        if subtype == "undelivered-candidate":
            candidate = {
                "kind": "unresolved-candidate",
                "reason": annotation.get("reason", "Undelivered candidate relation."),
                "note": (
                    "Migration candidate only; no certificate exists and this is not an "
                    "audit `unresolved` record."
                ),
            }
        pairs.append(
            {
                "pairId": pair_id,
                "theories": ordered,
                "legacy": {
                    "label": label,
                    "subtype": subtype,
                    "registry": registry,
                    "citation": citation,
                    "alsoListedIn": also_listed,
                    "duplicateRegistryRow": bool(also_listed),
                    "nonAuditMetadata": True,
                    "note": annotation.get(
                        "note",
                        "Legacy census label only; not an audit judgment.",
                    ),
                },
                "auditJudgment": None,
                "migration": {
                    "status": "not-audited",
                    "legacyLabelIsNotAnAuditJudgment": True,
                },
                "candidate": candidate,
                "ambiguous": (
                    {
                        "edgeReading": ambiguous["edge_reading"],
                        "absenceReading": ambiguous["absence_reading"],
                        "countedAs": ambiguous["counted_as"],
                        "effectOnCoverage": ambiguous["effect_on_coverage"],
                    }
                    if ambiguous
                    else None
                ),
            }
        )

    if len(pairs) != 136:
        raise InventoryError(f"generated {len(pairs)} pairs, expected 136")
    label_counts = {"edge": 0, "absence": 0, "unaccounted": 0}
    for row in pairs:
        label_counts[row["legacy"]["label"]] += 1
    raw_absence_rows = sum(len(rows) for rows in counts.ABSENCE_REGISTRIES.values())
    artifact = {
        "schemaVersion": SCHEMA_VERSION,
        "artifactKind": "relation-pair-inventory",
        "scope": "migration-inventory-only",
        "source": {
            "scanner": SCANNER,
            "scannerSha256": sha256_file(_path(root, SCANNER)),
            "theories": theories,
            "enumeration": [
                "tools/counts.py:THEORIES",
                "tools/counts.py:EDGES",
                "tools/counts.py:ABSENCE_REGISTRIES",
                "tools/counts.py:pair_census",
            ],
            "nonAuditMetadata": True,
        },
        "counts": {
            "pairs": len(pairs),
            "legacyEdges": label_counts["edge"],
            "legacyUniqueAbsences": label_counts["absence"],
            "legacyRawAbsenceRegistryRows": raw_absence_rows,
            "legacyCoveredPairs": label_counts["edge"] + label_counts["absence"],
            "unaccountedPairs": label_counts["unaccounted"],
            "bothEdgeAndAbsencePairs": len(census["both_edge_and_absence"]),
            "duplicateRegistryRows": len(census["registry_double_listings"]),
            "ambiguousPairs": len(census["ambiguous_pairs"]),
            "completionBlockPairs": census["completion_block_pairs"],
        },
        "unaccountedPairs": unaccounted,
        "bothEdgeAndAbsence": [list(pair) for pair in census["both_edge_and_absence"]],
        "pairs": pairs,
        "nonClaims": [
            "Legacy edge/absence labels are historical census labels, not audit judgments.",
            "No pair is recorded as certified, unresolved, notEstablished, or outOfScope.",
            "Coverage of the legacy census is not resolved audit coverage.",
        ],
    }
    return artifact


# ----------------------------------------------------------------------- validation


def validate_declaration_inventory(artifact: dict[str, Any]) -> list[Finding]:
    findings: list[Finding] = []
    counts = artifact.get("counts", {})
    declarations = artifact.get("declarations", [])
    sections = artifact.get("sections", [])

    def expect(key: str, actual: int) -> None:
        expected = EXPECTED[key]
        if actual != expected:
            findings.append(
                Finding(
                    f"inventory.count.{key}",
                    f"{key}: found {actual}, expected {expected} (scanner drift; do not regenerate blindly)",
                    artifact.get("artifactKind"),
                )
            )

    expect("declarations", counts.get("declarations"))
    expect("sections", counts.get("sections"))
    expect("sectionsWithDeclarations", counts.get("sectionsWithDeclarations"))
    if counts.get("documentationOnlySections") != EXPECTED["documentationOnlySections"]:
        findings.append(
            Finding(
                "inventory.count.documentationOnlySections",
                f"documentation-only sections {counts.get('documentationOnlySections')} != "
                f"{EXPECTED['documentationOnlySections']}",
                artifact.get("artifactKind"),
            )
        )
    if len(declarations) != len({row.get("declarationId") for row in declarations}):
        findings.append(Finding("inventory.declaration.duplicateId", "duplicate declaration ids"))
    if len(declarations) != len({row.get("name") for row in declarations}):
        findings.append(Finding("inventory.declaration.duplicateName", "duplicate declaration names"))
    for row in declarations:
        location = f"{row.get('sourceLocator', {}).get('artifact')}:{row.get('sourceLocator', {}).get('line')}"
        if not row.get("section"):
            findings.append(Finding("inventory.declaration.missingSection", "declaration has no section", location))
        if not row.get("sourceLocator") or not row["sourceLocator"].get("line"):
            findings.append(Finding("inventory.declaration.missingLocator", "declaration has no source locator", location))
        if row.get("legacy", {}).get("nonAuditMetadata") is not True:
            findings.append(Finding("inventory.declaration.legacyNamespace", "legacy metadata is not namespaced", location))
        if row.get("legacy", {}).get("class") in AUDIT_STATUS_WORDS | AUDIT_RELATION_KINDS:
            findings.append(Finding("inventory.declaration.legacyAuditVocabulary", "legacy class uses audit vocabulary", location))
    for section in sections:
        if section.get("declarationCount") != len(section.get("declarationIds", [])):
            findings.append(
                Finding(
                    "inventory.section.countMismatch",
                    f"section {section.get('number')} declarationCount does not match declarationIds",
                )
            )
    if sum(section.get("declarationCount", 0) for section in sections) != len(declarations):
        findings.append(Finding("inventory.section.sumMismatch", "section declaration counts do not sum to total"))
    return findings


def validate_pair_inventory(artifact: dict[str, Any]) -> list[Finding]:
    findings: list[Finding] = []
    counts = artifact.get("counts", {})
    pairs = artifact.get("pairs", [])
    expected_map = {
        "pairs": "pairs",
        "legacyEdges": "legacyEdges",
        "legacyUniqueAbsences": "legacyUniqueAbsences",
        "legacyCoveredPairs": "legacyCoveredPairs",
        "unaccountedPairs": "unaccountedPairs",
        "bothEdgeAndAbsencePairs": "bothEdgeAndAbsencePairs",
        "duplicateRegistryRows": "duplicateRegistryRows",
        "ambiguousPairs": "ambiguousPairs",
        "completionBlockPairs": "completionBlockPairs",
    }
    for key, expected_key in expected_map.items():
        actual = counts.get(key)
        expected = EXPECTED[expected_key]
        if actual != expected:
            findings.append(
                Finding(
                    f"inventory.count.{key}",
                    f"{key}: found {actual}, expected {expected} (scanner drift; do not regenerate blindly)",
                    artifact.get("artifactKind"),
                )
            )
    if len(pairs) != len({row.get("pairId") for row in pairs}):
        findings.append(Finding("inventory.pair.duplicateId", "duplicate pair ids"))
    if len(pairs) != len({tuple(row.get("theories", [])) for row in pairs}):
        findings.append(Finding("inventory.pair.duplicateTheories", "duplicate theory pairs"))
    for row in pairs:
        location = row.get("pairId")
        legacy = row.get("legacy", {})
        if legacy.get("label") not in {"edge", "absence"}:
            findings.append(Finding("inventory.pair.legacyLabel", f"unexpected legacy label {legacy.get('label')!r}", location))
        if legacy.get("nonAuditMetadata") is not True:
            findings.append(Finding("inventory.pair.legacyNamespace", "legacy metadata is not namespaced", location))
        if legacy.get("subtype") in AUDIT_STATUS_WORDS | AUDIT_RELATION_KINDS:
            findings.append(Finding("inventory.pair.legacyAuditVocabulary", "legacy subtype uses audit vocabulary", location))
        if row.get("auditJudgment") is not None:
            findings.append(Finding("inventory.pair.auditJudgment", "pair inventory must not carry an audit judgment", location))
        if row.get("migration", {}).get("status") != "not-audited":
            findings.append(Finding("inventory.pair.migrationStatus", "pair migration status must be not-audited", location))
        if legacy.get("label") == "unaccounted":
            findings.append(Finding("inventory.pair.unaccounted", "pair has neither a legacy edge nor a legacy absence", location))
    if artifact.get("unaccountedPairs"):
        findings.append(Finding("inventory.pair.unaccountedList", "unaccounted pair list is nonempty"))
    if artifact.get("bothEdgeAndAbsence"):
        findings.append(Finding("inventory.pair.both", "a pair is both an edge and an absence"))
    generated_keys = {frozenset(row.get("theories", [])) for row in pairs}
    for annotated in sorted(PAIR_ANNOTATIONS, key=lambda key: tuple(sorted(key))):
        if annotated not in generated_keys:
            findings.append(
                Finding(
                    "inventory.annotationUnknown",
                    f"pair annotation {sorted(annotated)} does not match a generated pair",
                    artifact.get("artifactKind"),
                )
            )
    return findings


def _load_dispositions_schema(root: str) -> json_schema.Schema:
    path = _path(root, DISPOSITIONS_SCHEMA)
    try:
        return json_schema.Schema.from_path(path)
    except (OSError, json.JSONDecodeError, json_schema.SchemaError) as exc:
        raise InventoryError(f"cannot load disposition schema {path}: {exc}") from exc


def _provenance_is_valid(entry: dict[str, Any]) -> bool:
    provenance = entry.get("provenance") or {}
    if provenance.get("kind") not in {"source", "manual", "computed", "imported"}:
        return False
    references = provenance.get("references") or []
    if not references:
        return False
    return all(ref.get("artifact") and ref.get("locator") for ref in references)


def validate_disposition_ledger(
    ledger: dict[str, Any],
    declaration_artifact: dict[str, Any],
    pair_artifact: dict[str, Any],
    pilot: dict[str, Any],
    root: str,
) -> list[Finding]:
    findings: list[Finding] = []
    schema = _load_dispositions_schema(root)
    for error in schema.validate(ledger):
        findings.append(Finding("disposition.schema", str(error), DISPOSITIONS))

    declarations = {row["name"]: row for row in declaration_artifact.get("declarations", [])}
    declaration_ids = {row["declarationId"] for row in declaration_artifact.get("declarations", [])}
    pair_ids = {row["pairId"] for row in pair_artifact.get("pairs", [])}
    pilot_records = {row["id"] for row in pilot.get("records", [])}
    pilot_queries = {row["id"] for row in pilot.get("queries", [])}
    disposition_ids = {row["id"] for row in DISPOSITION_VOCABULARY}
    role_ids = {row["id"] for row in RELATION_ROLE_VOCABULARY}

    entries = ledger.get("entries", [])
    seen_names: set[str] = set()
    seen_ids: set[str] = set()
    for index, entry in enumerate(entries):
        location = f"{DISPOSITIONS}:entries[{index}]"
        name = entry.get("name")
        if not isinstance(name, str):
            findings.append(Finding("disposition.name", "entry name must be a string", location))
            name = None
        if name is not None:
            if name in seen_names:
                findings.append(Finding("disposition.duplicate", f"declaration {name!r} appears more than once", location))
            seen_names.add(name)
            declaration = declarations.get(name)
            if declaration is None:
                findings.append(Finding("disposition.unknown", f"declaration {name!r} is not in the scanned relations inventory", location))
            else:
                if entry.get("declarationId") != declaration["declarationId"]:
                    findings.append(
                        Finding(
                            "disposition.idMismatch",
                            f"declaration {name!r}: id {entry.get('declarationId')!r} != {declaration['declarationId']!r}",
                            location,
                        )
                    )
                if entry.get("section") != declaration["section"]:
                    findings.append(
                        Finding(
                            "disposition.sectionMismatch",
                            f"declaration {name!r}: section {entry.get('section')!r} != {declaration['section']!r}",
                            location,
                        )
                    )
        declaration_id = entry.get("declarationId")
        if not isinstance(declaration_id, str):
            findings.append(Finding("disposition.id", "declarationId must be a string", location))
            declaration_id = None
        if declaration_id is not None:
            if declaration_id in seen_ids:
                findings.append(Finding("disposition.duplicateId", f"declaration id {declaration_id!r} appears more than once", location))
            seen_ids.add(declaration_id)
            if declaration_id not in declaration_ids:
                findings.append(Finding("disposition.unknownId", f"declaration id {declaration_id!r} is not in the inventory", location))
        if entry.get("disposition") not in disposition_ids:
            findings.append(Finding("disposition.invalid", f"unknown disposition {entry.get('disposition')!r}", location))
        if entry.get("relationRole") not in role_ids:
            findings.append(Finding("disposition.invalidRole", f"unknown relation role {entry.get('relationRole')!r}", location))
        if entry.get("disposition") in AUDIT_STATUS_WORDS:
            findings.append(Finding("disposition.auditVocabulary", "migration disposition uses an audit status", location))
        if entry.get("relationRole") in AUDIT_RELATION_KINDS:
            findings.append(Finding("disposition.auditVocabulary", "relation role uses a certified relation kind", location))
        if not isinstance(entry.get("rationale"), str) or len(entry.get("rationale", "").strip()) < 40:
            findings.append(Finding("disposition.rationale", "rationale is missing or too short", location))
        if not _provenance_is_valid(entry):
            findings.append(Finding("disposition.provenance", "provenance is missing or invalid", location))
        pair_ids_value = entry.get("pairIds") if isinstance(entry.get("pairIds"), list) else []
        for pair_id in pair_ids_value:
            if pair_id not in pair_ids:
                findings.append(Finding("disposition.pairUnknown", f"unknown pair id {pair_id!r}", location))
        related_pair_ids_value = (
            entry.get("relatedPairIds") if isinstance(entry.get("relatedPairIds"), list) else []
        )
        for pair_id in related_pair_ids_value:
            if pair_id not in pair_ids:
                findings.append(Finding("disposition.relatedPairUnknown", f"unknown related pair id {pair_id!r}", location))
        pilot_record_ids_value = (
            entry.get("pilotRecordIds") if isinstance(entry.get("pilotRecordIds"), list) else []
        )
        for record_id in pilot_record_ids_value:
            if record_id not in pilot_records:
                findings.append(Finding("disposition.pilotRecordUnknown", f"unknown pilot record {record_id!r}", location))
        pilot_query_ids_value = (
            entry.get("pilotQueryIds") if isinstance(entry.get("pilotQueryIds"), list) else []
        )
        for query_id in pilot_query_ids_value:
            if query_id not in pilot_queries:
                findings.append(Finding("disposition.pilotQueryUnknown", f"unknown pilot query {query_id!r}", location))
        if entry.get("intraTheory") and entry.get("pairIds"):
            findings.append(Finding("disposition.intraTheoryPair", "intra-theory entry must not claim a cross-theory pair id", location))
        association = entry.get("pairAssociation")
        if association not in {"direct", "supporting", "look-alike", "intra-theory", "transitive", "none"}:
            findings.append(Finding("disposition.pairAssociation", f"unknown pair association {association!r}", location))
        if entry.get("intraTheory") and association != "intra-theory":
            findings.append(Finding("disposition.pairAssociationIntra", "intraTheory entry must use pairAssociation intra-theory", location))
        if not entry.get("intraTheory") and association == "intra-theory":
            findings.append(Finding("disposition.pairAssociationIntra", "pairAssociation intra-theory requires intraTheory true", location))
        if association in {"direct", "look-alike", "transitive"} and not (entry.get("pairIds") or entry.get("relatedPairIds")):
            findings.append(Finding("disposition.pairAssociationEvidence", f"pairAssociation {association!r} needs a pair reference", location))
        if association == "supporting" and not (entry.get("pairIds") or entry.get("relatedPairIds")):
            findings.append(Finding("disposition.pairAssociationEvidence", "supporting pair association needs a pair reference", location))
        if association == "none" and (entry.get("pairIds") or entry.get("relatedPairIds")):
            findings.append(Finding("disposition.pairAssociationNone", "pairAssociation none must not carry a pair reference", location))
        if entry.get("disposition") == "pilot-certificate" and not entry.get("pilotRecordIds"):
            findings.append(Finding("disposition.pilotEvidence", "pilot-certificate disposition needs a pilot record id", location))
        if entry.get("nonAuditMetadata") is not True:
            findings.append(Finding("disposition.nonAuditMetadata", "entry must be marked non-audit metadata", location))

    missing = sorted(set(declarations) - seen_names)
    for name in missing:
        findings.append(
            Finding(
                "disposition.missing",
                f"scanned declaration {name!r} has no disposition entry",
                declarations[name]["sourceLocator"].get("artifact"),
            )
        )
    if len(entries) != EXPECTED["declarations"]:
        findings.append(
            Finding(
                "disposition.count",
                f"{len(entries)} disposition entries for {EXPECTED['declarations']} declarations",
                DISPOSITIONS,
            )
        )
    return findings


def validate_disposition_counts(ledger: dict[str, Any], report: dict[str, Any]) -> list[Finding]:
    findings: list[Finding] = []
    computed: dict[str, int] = {row["id"]: 0 for row in DISPOSITION_VOCABULARY}
    for entry in ledger.get("entries", []):
        disposition = entry.get("disposition")
        if isinstance(disposition, str):
            computed[disposition] = computed.get(disposition, 0) + 1
    if sum(computed.values()) != EXPECTED["declarations"]:
        findings.append(Finding("report.dispositionTotal", "disposition counts do not sum to 78"))
    if report.get("dispositionCounts") != computed:
        findings.append(Finding("report.dispositionCounts", "report disposition counts do not match the ledger"))
    return findings


# --------------------------------------------------------------------------- report


def _hash_artifact_text(artifact: dict[str, Any]) -> str:
    return sha256_text(json_text(artifact))


def build_report(
    root: str,
    declaration_artifact: dict[str, Any],
    pair_artifact: dict[str, Any],
    ledger: dict[str, Any],
) -> dict[str, Any]:
    entries = ledger.get("entries", [])
    disposition_counts: dict[str, int] = {row["id"]: 0 for row in DISPOSITION_VOCABULARY}
    role_counts: dict[str, int] = {row["id"]: 0 for row in RELATION_ROLE_VOCABULARY}
    association_counts: dict[str, int] = {
        "direct": 0, "supporting": 0, "look-alike": 0, "intra-theory": 0,
        "transitive": 0, "none": 0,
    }
    for entry in entries:
        disposition = entry.get("disposition")
        if isinstance(disposition, str):
            disposition_counts[disposition] = disposition_counts.get(disposition, 0) + 1
        role = entry.get("relationRole")
        if isinstance(role, str):
            role_counts[role] = role_counts.get(role, 0) + 1
        association = entry.get("pairAssociation")
        if isinstance(association, str):
            association_counts[association] = association_counts.get(association, 0) + 1

    section_by_number = {section["number"]: section for section in declaration_artifact.get("sections", [])}
    section_stats = []
    for section in declaration_artifact.get("sections", []):
        section_entries = [entry for entry in entries if entry.get("section") == section["number"]]
        stats = {"declarations": len(section_entries)}
        for row in DISPOSITION_VOCABULARY:
            stats[row["id"]] = len([entry for entry in section_entries if entry.get("disposition") == row["id"]])
        section_stats.append(
            {
                "number": section["number"],
                "title": section["title"],
                "declarationCount": section["declarationCount"],
                "legacyClass": section["legacyClass"],
                "documentationOnly": section["documentationOnly"],
                "dispositions": stats,
            }
        )

    subtype_groups: dict[str, list[str]] = {}
    for pair in pair_artifact.get("pairs", []):
        subtype = pair["legacy"]["subtype"]
        subtype_groups.setdefault(subtype, []).append(pair["pairId"])

    undelivered = [
        {
            "pairId": pair["pairId"],
            "theories": pair["theories"],
            "reason": pair["candidate"]["reason"],
        }
        for pair in pair_artifact.get("pairs", [])
        if pair.get("candidate")
    ]
    ambiguous = [
        {
            "pairId": pair["pairId"],
            "theories": pair["theories"],
            "edgeReading": pair["ambiguous"]["edgeReading"],
            "absenceReading": pair["ambiguous"]["absenceReading"],
            "countedAs": pair["ambiguous"]["countedAs"],
            "effectOnCoverage": pair["ambiguous"]["effectOnCoverage"],
        }
        for pair in pair_artifact.get("pairs", [])
        if pair.get("ambiguous")
    ]
    duplicate_rows = [
        {
            "pairId": pair["pairId"],
            "theories": pair["theories"],
            "alsoListedIn": pair["legacy"]["alsoListedIn"],
        }
        for pair in pair_artifact.get("pairs", [])
        if pair["legacy"].get("duplicateRegistryRow")
    ]
    pilot_mapped = [
        {
            "declarationId": entry.get("declarationId"),
            "name": entry.get("name"),
            "pilotRecordIds": entry.get("pilotRecordIds") or [],
            "pilotQueryIds": entry.get("pilotQueryIds") or [],
        }
        for entry in entries
        if entry.get("pilotRecordIds")
    ]
    intra_theory = [
        {
            "declarationId": entry.get("declarationId"),
            "name": entry.get("name"),
            "relationRole": entry.get("relationRole"),
        }
        for entry in entries
        if entry.get("intraTheory")
    ]

    declarations = declaration_artifact["counts"]
    pairs = pair_artifact["counts"]
    report = {
        "schemaVersion": SCHEMA_VERSION,
        "reportKind": "relation-audit-migration-inventory-report",
        "scope": "inventory-only",
        "status": "INVENTORY_ONLY",
        "coverage": {
            "fullRegistryCreated": False,
            "registryPath": None,
            "resolvedCoverageClaimed": False,
            "fullRegistryPassClaimed": False,
            "note": (
                "The 136-pair list is the legacy census universe, not resolved audit coverage. "
                "No production registry.json and no 136/136 resolved-coverage claim are made."
            ),
        },
        "sourceOfTruth": {
            "scanner": SCANNER,
            "scannerSha256": declaration_artifact["source"]["scannerSha256"],
            "relations": RELATIONS,
            "relationsSha256": declaration_artifact["source"]["relationsSha256"],
            "dispositions": DISPOSITIONS,
            "dispositionsSha256": sha256_file(_path(root, DISPOSITIONS)),
            "dispositionSchema": DISPOSITIONS_SCHEMA,
            "pilot": PILOT,
            "pilotSha256": sha256_file(_path(root, PILOT)),
            "functions": sorted(
                set(declaration_artifact["source"]["enumeration"])
                | set(pair_artifact["source"]["enumeration"])
            ),
        },
        "generatedArtifacts": {
            "declarations": GENERATED_DECLARATIONS,
            "declarationsSha256": _hash_artifact_text(declaration_artifact),
            "pairs": GENERATED_PAIRS,
            "pairsSha256": _hash_artifact_text(pair_artifact),
        },
        "counts": {
            "declarations": declarations["declarations"],
            "sections": declarations["sections"],
            "sectionsWithDeclarations": declarations["sectionsWithDeclarations"],
            "documentationOnlySections": declarations["documentationOnlySections"],
            "pairs": pairs["pairs"],
            "legacyEdges": pairs["legacyEdges"],
            "legacyUniqueAbsences": pairs["legacyUniqueAbsences"],
            "legacyRawAbsenceRegistryRows": pairs["legacyRawAbsenceRegistryRows"],
            "legacyCoveredPairs": pairs["legacyCoveredPairs"],
            "unaccountedPairs": pairs["unaccountedPairs"],
            "bothEdgeAndAbsencePairs": pairs["bothEdgeAndAbsencePairs"],
            "duplicateRegistryRows": pairs["duplicateRegistryRows"],
            "ambiguousPairs": pairs["ambiguousPairs"],
            "completionBlockPairs": pairs["completionBlockPairs"],
            "legacyClassTotals": declarations["legacyClassTotals"],
            "legacyQuotedClassTotals": declarations["legacyQuotedClassTotals"],
            "legacyClassVerdicts": declarations["legacyClassVerdicts"],
            "dispositionEntries": len(entries),
            "declarationsWithPairIds": len([entry for entry in entries if entry.get("pairIds")]),
            "declarationsWithoutPairIds": len([entry for entry in entries if not entry.get("pairIds")]),
            "intraTheoryDeclarations": len(intra_theory),
            "pilotMappedDeclarations": len(pilot_mapped),
            "unresolvedCandidateDeclarations": disposition_counts.get("unresolved-candidate", 0),
        },
        "dispositionCounts": disposition_counts,
        "roleCounts": role_counts,
        "pairAssociationCounts": association_counts,
        "sectionStats": section_stats,
        "legacyPairCensus": {
            "pairs": pairs["pairs"],
            "edges": pairs["legacyEdges"],
            "uniqueAbsences": pairs["legacyUniqueAbsences"],
            "rawAbsenceRegistryRows": pairs["legacyRawAbsenceRegistryRows"],
            "covered": pairs["legacyCoveredPairs"],
            "unaccounted": pairs["unaccountedPairs"],
            "bothEdgeAndAbsence": pairs["bothEdgeAndAbsencePairs"],
            "legacyCensusComplete": (
                pairs["legacyCoveredPairs"] == 136
                and pairs["unaccountedPairs"] == 0
                and pairs["bothEdgeAndAbsencePairs"] == 0
            ),
            "scope": "legacy-census-only",
            "note": "This is historical edge/absence census completeness, not audit coverage.",
        },
        "legacySubtypeCounts": {key: len(value) for key, value in sorted(subtype_groups.items())},
        "exceptionalClassifications": {
            key: value
            for key, value in sorted(subtype_groups.items())
            if key not in {"direct-edge", "registered-absence", "direct"}
        },
        "undeliveredCandidates": undelivered,
        "ambiguousCases": ambiguous,
        "duplicateRegistryRows": duplicate_rows,
        "pilotMappedDeclarations": pilot_mapped,
        "intraTheoryDeclarations": intra_theory,
        "nonClaims": [
            "This inventory is not a production full registry; relation_audit/registry.json is not created.",
            "No 136/136 resolved-coverage claim is made; the pair list is a legacy census universe.",
            "Legacy edge/absence labels are not audit judgments and are not mapped to certified/notEstablished/outOfScope.",
            "No new Lean certificate wrapper is added and no legacy edge is claimed migrated.",
            "Undelivered candidates are migration items only; they are not audit `unresolved` records.",
            "An inventory --check exit code 0 means the artifacts are consistent with tools/counts.py, not that the relation audit passed.",
            "The census remains a report, not an acceptance gate.",
        ],
    }
    return report


# ----------------------------------------------------------------------------- check


def _compare_file(root: str, relative: str, expected_text: str) -> list[Finding]:
    path = _path(root, relative)
    if not os.path.isfile(path):
        return [Finding("drift.missing", f"{relative} is missing", relative)]
    with open(path, encoding="utf-8") as handle:
        actual = handle.read()
    if actual != expected_text:
        return [
            Finding(
                "drift.mismatch",
                f"{relative} is stale; rerun --generate and inspect the scanner drift before accepting it",
                relative,
            )
        ]
    return []


def _render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Relation-Audit Migration Inventory Report (R2)",
        "",
        "Status: **inventory only** — this is not a production registry and not an audit verdict.",
        "",
        "## Source of truth",
        "",
        f"- scanner: `{report['sourceOfTruth']['scanner']}` (`{report['sourceOfTruth']['scannerSha256'][:12]}…`)",
        f"- relations module: `{report['sourceOfTruth']['relations']}` (`{report['sourceOfTruth']['relationsSha256'][:12]}…`)",
        f"- disposition ledger: `{report['sourceOfTruth']['dispositions']}` (`{report['sourceOfTruth']['dispositionsSha256'][:12]}…`)",
        "",
        "## Counts",
        "",
        "| item | value |",
        "|---|---|",
    ]
    for key in (
        "declarations",
        "sections",
        "sectionsWithDeclarations",
        "pairs",
        "legacyEdges",
        "legacyUniqueAbsences",
        "legacyRawAbsenceRegistryRows",
        "legacyCoveredPairs",
        "unaccountedPairs",
        "bothEdgeAndAbsencePairs",
        "duplicateRegistryRows",
        "ambiguousPairs",
        "completionBlockPairs",
        "dispositionEntries",
        "intraTheoryDeclarations",
        "pilotMappedDeclarations",
        "unresolvedCandidateDeclarations",
    ):
        lines.append(f"| {key} | {report['counts'][key]} |")
    lines += ["", "## Dispositions", "", "| disposition | declarations |", "|---|---|"]
    for key, value in report["dispositionCounts"].items():
        lines.append(f"| `{key}` | {value} |")
    lines += ["", "## Pair association", "", "| association | declarations |", "|---|---|"]
    for key, value in report["pairAssociationCounts"].items():
        lines.append(f"| `{key}` | {value} |")
    lines += ["", "## Legacy pair census", ""]
    lines.append(
        f"{report['legacyPairCensus']['edges']} edges + "
        f"{report['legacyPairCensus']['uniqueAbsences']} unique absences = "
        f"{report['legacyPairCensus']['covered']}/{report['legacyPairCensus']['pairs']} covered "
        f"(legacy census, not audit coverage); "
        f"unaccounted {report['legacyPairCensus']['unaccounted']}, "
        f"edge∩absence {report['legacyPairCensus']['bothEdgeAndAbsence']}."
    )
    lines += ["", "## Legacy declaration class mapping (non-audit)", ""]
    quoted = report["counts"]["legacyQuotedClassTotals"]
    computed = report["counts"]["legacyClassTotals"]
    verdicts = report["counts"]["legacyClassVerdicts"]
    lines += ["| class | quoted | computed | verdict |", "|---|---|---|---|"]
    for key in sorted(quoted):
        lines.append(f"| `{key}` | {quoted[key]} | {computed.get(key, 0)} | {verdicts.get(key, '—')} |")
    lines += ["", "## Exceptional classifications", ""]
    if report["exceptionalClassifications"]:
        for key, values in report["exceptionalClassifications"].items():
            lines.append(f"- `{key}`: {', '.join(f'`{value}`' for value in values)}")
    else:
        lines.append("- none")
    lines += ["", "## Undelivered candidates", ""]
    if report["undeliveredCandidates"]:
        for row in report["undeliveredCandidates"]:
            lines.append(f"- `{row['pairId']}` ({' / '.join(row['theories'])}): {row['reason']}")
    else:
        lines.append("- none")
    lines += ["", "## Ambiguous cases", ""]
    if report["ambiguousCases"]:
        for row in report["ambiguousCases"]:
            lines.append(
                f"- `{row['pairId']}` counted as `{row['countedAs']}`: "
                f"{row['effectOnCoverage']}"
            )
    else:
        lines.append("- none")
    lines += ["", "## Duplicate registry rows", ""]
    if report["duplicateRegistryRows"]:
        for row in report["duplicateRegistryRows"]:
            lines.append(f"- `{row['pairId']}`: listed {len(row['alsoListedIn'])} times")
    else:
        lines.append("- none")
    lines += ["", "## Non-claims", ""]
    for item in report["nonClaims"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def build_all(
    root: str,
) -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    """Build the declaration inventory, pair inventory, ledger, pilot, and report."""
    counts = load_counts_module(root)
    declarations = build_declaration_inventory(root, counts)
    pairs = build_pair_inventory(root, counts)
    ledger = load_json(_path(root, DISPOSITIONS))
    pilot = load_json(_path(root, PILOT))
    if not isinstance(ledger, dict) or not isinstance(ledger.get("entries"), list):
        raise InventoryError("dispositions.json must be an object with an entries array")
    if any(not isinstance(entry, dict) for entry in ledger["entries"]):
        raise InventoryError("every dispositions entry must be a JSON object")
    if not isinstance(pilot, dict) or not isinstance(pilot.get("records"), list)             or not isinstance(pilot.get("queries"), list):
        raise InventoryError("pilot.json must be an object with records and queries arrays")
    report = build_report(root, declarations, pairs, ledger)
    return declarations, pairs, ledger, report, pilot


def collect_findings(
    root: str,
    declarations: dict[str, Any],
    pairs: dict[str, Any],
    ledger: dict[str, Any],
    report: dict[str, Any],
    pilot: dict[str, Any],
) -> list[Finding]:
    findings: list[Finding] = []
    findings.extend(validate_declaration_inventory(declarations))
    findings.extend(validate_pair_inventory(pairs))
    findings.extend(validate_disposition_ledger(ledger, declarations, pairs, pilot, root))
    findings.extend(validate_disposition_counts(ledger, report))
    # The report must never claim registry coverage or a full-registry pass.
    coverage = report.get("coverage", {})
    for key in ("fullRegistryCreated", "resolvedCoverageClaimed", "fullRegistryPassClaimed"):
        if coverage.get(key) is not False:
            findings.append(Finding("report.coverageClaim", f"report coverage.{key} must be false"))
    if report.get("status") != "INVENTORY_ONLY":
        findings.append(Finding("report.status", "report status must be INVENTORY_ONLY"))
    return findings


def generate(root: str) -> int:
    declarations, pairs, ledger, report, pilot = build_all(root)  # type: ignore[misc]
    findings = collect_findings(root, declarations, pairs, ledger, report, pilot)
    if findings:
        for finding in findings:
            print(finding)
        print(f"inventory generation refused: {len(findings)} finding(s)")
        return 1
    report_text = json_text(report)
    markdown = _render_markdown(report)
    outputs = [
        (GENERATED_DECLARATIONS, json_text(declarations)),
        (GENERATED_PAIRS, json_text(pairs)),
        (REPORT_JSON, report_text),
        (REPORT_MD, markdown),
    ]
    for relative, text in outputs:
        path = _path(root, relative)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(text)
    print(
        "inventory generated: "
        f"{declarations['counts']['declarations']} declarations, "
        f"{declarations['counts']['sections']} sections, "
        f"{pairs['counts']['pairs']} pairs "
        f"({pairs['counts']['legacyEdges']} legacy edges + "
        f"{pairs['counts']['legacyUniqueAbsences']} unique legacy absences)"
    )
    for relative, _ in outputs:
        print(f"  wrote {relative}")
    print("scope: inventory only; no production registry and no audit coverage claim")
    return 0


def check(root: str) -> int:
    declarations, pairs, ledger, report, pilot = build_all(root)  # type: ignore[misc]
    findings = collect_findings(root, declarations, pairs, ledger, report, pilot)
    findings.extend(_compare_file(root, GENERATED_DECLARATIONS, json_text(declarations)))
    findings.extend(_compare_file(root, GENERATED_PAIRS, json_text(pairs)))
    findings.extend(_compare_file(root, REPORT_JSON, json_text(report)))
    findings.extend(_compare_file(root, REPORT_MD, _render_markdown(report)))
    if findings:
        for finding in findings:
            print(finding)
        print(f"inventory check: {len(findings)} finding(s)")
        return 1
    print(
        "inventory check: OK "
        f"({declarations['counts']['declarations']} declarations, "
        f"{declarations['counts']['sections']} sections, "
        f"{pairs['counts']['pairs']} pairs; inventory-only, not an audit verdict)"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="relation_audit_inventory.py",
        description=(
            "Single-source declaration/pair inventory and disposition checker for the "
            "PhotoLean relation audit. It derives every row from tools/counts.py."
        ),
    )
    parser.add_argument("--generate", action="store_true", help="write the generated inventories and report")
    parser.add_argument("--check", action="store_true", help="check scanner consistency and checked-in drift (default)")
    parser.add_argument("--repo-root", default=None, help="repository root (default: the checkout containing this tool)")
    parser.add_argument("--quiet", action="store_true", help="only print the final line")
    args = parser.parse_args(argv)
    if args.generate and args.check:
        parser.error("--generate and --check are mutually exclusive")
    try:
        root = args.repo_root or repo_root(__file__)
        mode = "generate" if args.generate else "check"
        if args.quiet and mode == "check":
            # Preserve the fail-closed exit code but keep stdout to the final line.
            import contextlib
            import io

            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                code = generate(root) if mode == "generate" else check(root)
            lines = buffer.getvalue().strip().splitlines()
            print(lines[-1] if lines else ("inventory check: OK" if code == 0 else "inventory check: FAILED"))
            return code
        return generate(root) if mode == "generate" else check(root)
    except InventoryError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    except (OSError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())

"""R3 migration-fragment integration checker and Lean-check generator.

The R3 section workers authored three Lean modules and three JSON fragments.  The
fragments are the single source of truth for what the integration layer knows:
the generator below derives every Lean command from them, so there is no second
hand-maintained certificate list.

The checker is deliberately fail closed.  It rejects a fragment set when any of
the following holds:

* the 41 R2 ``certificate-required`` declaration IDs are not covered exactly
  once across the fragments (duplicate, omission, unknown ID, wrong R2
  disposition, or section drift);
* a ``certified`` entry has no certificate, a kind outside the seven-kind
  vocabulary, an inconsistent constructor/module/witness field, a duplicate
  premise ID, a disallowed axiom footprint, or a definitional-identity entry
  without a fresh ``DefEq.refl`` witness;
* a ``reclassified`` entry still carries a certificate, has no target category,
  has a short or duplicated rationale, has no certification blocker, or has no
  Lean evidence re-export;
* a conditional-composition certificate lacks its canonical projection
  metadata, or the declared composition form is not the form implied by its
  typed parents;
* a declared ``leanSourceSha256`` no longer matches the section module (the
  fragment went stale).

Commands (run from the repository root)::

    python3 tools/relation_audit_migration.py --check
    python3 tools/relation_audit_migration.py --generate
    python3 tools/relation_audit_migration.py --check --lean

``--generate`` writes the report and the generated Lean check file.
``--check --lean`` additionally builds ``PhotoLean.RelationAudit.Full`` and
elaborates the checked-in generated file, comparing every ``#print axioms``
footprint with the fragment's declared footprint.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from typing import Any, Iterable


SCHEMA_VERSION = "1.0.0"
EXPECTED_QUEUE_SIZE = 41

RELATIONS = "PhotoLean/Relations.lean"
DISPOSITIONS = "relation_audit/dispositions.json"
FRAGMENTS = (
    ("sections01_05", "relation_audit/migration/sections01_05.json"),
    ("sections06_10", "relation_audit/migration/sections06_10.json"),
    ("sections11_17", "relation_audit/migration/sections11_17.json"),
)
REPORT_JSON = "relation_audit/reports/migration-report.json"
REPORT_MD = "relation_audit/reports/migration-report.md"
LEAN_OUT = "relation_audit/reports/migration-lean-checks.lean"
FULL_MODULE = "PhotoLean.RelationAudit.Full"

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
RELATION_KINDS = (
    "definitionalIdentity",
    "implication",
    "equivalence",
    "conditionalComposition",
    "observationalEquivalence",
    "distinguishability",
    "refutation",
)
COMPOSITION_PARENT_KINDS = frozenset({"implication", "equivalence"})
# R2 roles that must never be promoted to a certificate: they are transitive
# tie-backs, support facts, intra-theory bridges, look-alikes, one-sided notes,
# or model-level composition rows. A certified row with one of these roles is a
# semantic regression even when the Lean term happens to typecheck.
NON_CERTIFIABLE_R2_ROLES = frozenset(
    {
        "transitive-tie-back",
        "support",
        "composition-component",
        "intra-theory-bridge",
        "intra-theory-adjudication",
        "adjudication-verdict",
        "adjudication-boundary",
        "look-alike-shared-form",
        "look-alike-contrast",
        "shape-note",
        "one-sided-note",
        "model-level-composition",
    }
)
CERTIFICATE_CONSTRUCTOR_PREFIX = "PhotoLean.RelationAudit.RelationKind."
KIND_FUNCTION = "PhotoLean.RelationAudit.certificateKind"
PREMISE_FUNCTION = "PhotoLean.RelationAudit.certificatePremiseIDs"
MIN_RATIONALE_CHARS = 200
MIN_RATIONALE_WORDS = 25
PLACEHOLDER_TOKENS = ("todo", "tbd", "fixme", "placeholder", "n/a")

NON_CLAIMS = [
    "This report is not a production full registry and does not claim 136/136 "
    "or resolved coverage.",
    "The queue covers exactly the 41 R2 certificate-required declarations, not "
    "all 78 scanned declarations and not the 136-pair universe.",
    "Reclassified rows are not certified relations; their Lean names are "
    "evidence re-exports only and deliberately are not Certificate values.",
    "No conditionalComposition certificate is created in R3; the generator "
    "supports its canonical projections but emits none for these fragments.",
    "A definitionalIdentity certificate is a fresh DefEq/rfl check, not "
    "propositional equality and not a physical-identity claim.",
    "An observationalEquivalence certificate records agreement on the declared "
    "channels and is not a propositional equivalence.",
    "A generated #print axioms footprint check covers only the named "
    "declarations; it is not a whole-repository proof or audit verdict.",
    "The R1 pilot, R2 inventory, original theory modules, dispositions, schema "
    "and manuscript are unchanged by this integration round.",
]


class MigrationError(Exception):
    """Raised when the fragment set cannot be loaded at all."""


class Finding:
    """One fail-closed integration finding."""

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
            raise MigrationError(f"cannot locate repository root above {start!r}")
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


# ------------------------------------------------------------------------ loading


def load_dispositions(root: str) -> dict[str, Any]:
    path = _path(root, DISPOSITIONS)
    data = load_json(path)
    if not isinstance(data, dict) or not isinstance(data.get("entries"), list):
        raise MigrationError(f"{DISPOSITIONS} must be an object with an entries array")
    return data


def load_fragments(root: str) -> list[dict[str, Any]]:
    fragments: list[dict[str, Any]] = []
    for name, relative in FRAGMENTS:
        path = _path(root, relative)
        if not os.path.isfile(path):
            raise MigrationError(f"missing migration fragment {relative}")
        data = load_json(path)
        if not isinstance(data, dict):
            raise MigrationError(f"{relative} must be a JSON object")
        data = dict(data)
        data["_fragmentName"] = name
        data["_fragmentPath"] = relative
        fragments.append(data)
    return fragments


def queue_entries(dispositions: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        entry
        for entry in dispositions.get("entries", [])
        if isinstance(entry, dict) and entry.get("disposition") == "certificate-required"
    ]


def _entries(fragments: Iterable[dict[str, Any]]) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    pairs: list[tuple[dict[str, Any], dict[str, Any]]] = []
    for fragment in fragments:
        entries = fragment.get("entries")
        if not isinstance(entries, list):
            continue
        for entry in entries:
            if isinstance(entry, dict):
                pairs.append((fragment, entry))
    return pairs


# ---------------------------------------------------------------------- validation


def _valid_text(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _word_count(text: str) -> int:
    return len(re.findall(r"[A-Za-z0-9_]+", text))


def _premise_ids(entry: dict[str, Any]) -> list[str]:
    premises = entry.get("premises")
    if not isinstance(premises, list):
        return []
    ids: list[str] = []
    for premise in premises:
        if isinstance(premise, dict) and isinstance(premise.get("id"), str):
            ids.append(premise["id"])
    return ids


def _duplicates(values: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    duplicates: list[str] = []
    for value in values:
        if value in seen and value not in duplicates:
            duplicates.append(value)
        seen.add(value)
    return duplicates


def _target_category_vocabulary(fragment: dict[str, Any]) -> set[str]:
    vocabulary: set[str] = set()
    rows = fragment.get("targetCategoryVocabulary")
    if isinstance(rows, list):
        for row in rows:
            if isinstance(row, dict) and _valid_text(row.get("id")):
                vocabulary.add(row["id"])
            elif isinstance(row, str):
                vocabulary.add(row)
    return vocabulary


def _composition_metadata(entry: dict[str, Any]) -> dict[str, Any] | None:
    metadata = entry.get("composition")
    return metadata if isinstance(metadata, dict) else None


def validate_fragments(
    fragments: list[dict[str, Any]],
    dispositions: dict[str, Any],
    *,
    relations_source: str | None = None,
) -> list[Finding]:
    """Validate queue coverage and every fragment entry.  Pure, deterministic."""
    findings: list[Finding] = []
    queue = queue_entries(dispositions)
    queue_ids = [entry.get("declarationId") for entry in queue]
    queue_set = {value for value in queue_ids if isinstance(value, str)}

    if len(queue_ids) != EXPECTED_QUEUE_SIZE:
        findings.append(
            Finding(
                "migration.queueCount",
                f"dispositions.json has {len(queue_ids)} certificate-required rows; "
                f"the R3 contract fixes {EXPECTED_QUEUE_SIZE}",
                DISPOSITIONS,
            )
        )
    if len(queue_set) != len(queue_ids):
        findings.append(
            Finding(
                "migration.queueDuplicate",
                "dispositions.json repeats a certificate-required declaration ID",
                DISPOSITIONS,
            )
        )

    known = {
        entry.get("declarationId"): entry
        for entry in dispositions.get("entries", [])
        if isinstance(entry, dict) and isinstance(entry.get("declarationId"), str)
    }

    all_seen: dict[str, str] = {}
    all_rationales: dict[str, str] = {}
    section_members: dict[str, int] = {}

    for fragment in fragments:
        name = fragment.get("_fragmentName") or fragment.get("module") or "<fragment>"
        location = fragment.get("_fragmentPath") or name
        entries = fragment.get("entries")
        if not isinstance(entries, list):
            findings.append(Finding("migration.fragmentStructure", "entries must be an array", location))
            continue

        if fragment.get("artifactKind") != "relation-migration-fragment":
            findings.append(
                Finding(
                    "migration.fragmentStructure",
                    "artifactKind must be 'relation-migration-fragment'",
                    location,
                )
            )
        module = fragment.get("module")
        if not _valid_text(module) or not module.startswith("PhotoLean.RelationAudit.Full."):
            findings.append(
                Finding(
                    "migration.fragmentModule",
                    f"module must be in PhotoLean.RelationAudit.Full.*, got {module!r}",
                    location,
                )
            )
        section_range = fragment.get("sectionRange")
        first = last = None
        if isinstance(section_range, dict):
            first, last = section_range.get("first"), section_range.get("last")
        if not isinstance(first, int) or not isinstance(last, int) or first > last:
            findings.append(
                Finding("migration.sectionRange", "sectionRange must carry integers first <= last", location)
            )

        queue_block = fragment.get("queue")
        if not isinstance(queue_block, dict):
            findings.append(Finding("migration.fragmentQueue", "queue must be an object", location))
            queue_block = {}
        declared_ids = queue_block.get("declarationIds")
        if not isinstance(declared_ids, list) or not all(isinstance(item, str) for item in declared_ids):
            findings.append(
                Finding("migration.fragmentQueue", "queue.declarationIds must be a string array", location)
            )
            declared_ids = []
        entry_ids: list[str] = []
        for index, entry in enumerate(entries):
            if not isinstance(entry, dict):
                findings.append(
                    Finding("migration.fragmentStructure", f"entry {index} is not an object", location)
                )
                continue
            declaration_id = entry.get("declarationId")
            if not _valid_text(declaration_id):
                findings.append(
                    Finding("migration.entryStructure", f"entry {index} has no declarationId", location)
                )
                continue
            entry_ids.append(declaration_id)
        if declared_ids != entry_ids:
            findings.append(
                Finding(
                    "migration.fragmentQueue",
                    "queue.declarationIds and fragment entries are not in one-to-one order",
                    location,
                )
            )
        expected_count = queue_block.get("expectedCount")
        covered_count = queue_block.get("coveredCount")
        if expected_count != len(declared_ids):
            findings.append(
                Finding(
                    "migration.fragmentQueue",
                    f"queue.expectedCount={expected_count!r} but queue has {len(declared_ids)} IDs",
                    location,
                )
            )
        if covered_count != len(entries):
            findings.append(
                Finding(
                    "migration.fragmentQueue",
                    f"queue.coveredCount={covered_count!r} but fragment has {len(entries)} entries",
                    location,
                )
            )

        actual_outcomes: dict[str, int] = {"certified": 0, "reclassified": 0}
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            outcome = entry.get("outcome")
            if outcome in actual_outcomes:
                actual_outcomes[outcome] += 1
        declared_outcomes = queue_block.get("outcomeCounts")
        if declared_outcomes != actual_outcomes:
            findings.append(
                Finding(
                    "migration.fragmentQueue",
                    f"queue.outcomeCounts={declared_outcomes!r} but entries count {actual_outcomes!r}",
                    location,
                )
            )

        for entry in entries:
            if not isinstance(entry, dict):
                continue
            declaration_id = entry.get("declarationId")
            if not _valid_text(declaration_id):
                continue
            where = f"{location}#{declaration_id}"
            if declaration_id in all_seen:
                findings.append(
                    Finding(
                        "migration.duplicateDeclarationId",
                        f"{declaration_id} also occurs in {all_seen[declaration_id]}",
                        where,
                    )
                )
            else:
                all_seen[declaration_id] = location
            section_members[declaration_id] = section_members.get(declaration_id, 0) + 1

            if declaration_id not in known:
                findings.append(
                    Finding(
                        "migration.unknownDeclarationId",
                        f"{declaration_id} is not in dispositions.json",
                        where,
                    )
                )
            else:
                ledger_row = known[declaration_id]
                if ledger_row.get("disposition") != "certificate-required":
                    findings.append(
                        Finding(
                            "migration.wrongDisposition",
                            f"{declaration_id} has R2 disposition {ledger_row.get('disposition')!r}",
                            where,
                        )
                    )
                if ledger_row.get("section") != entry.get("section"):
                    findings.append(
                        Finding(
                            "migration.sectionMismatch",
                            f"{declaration_id} section {entry.get('section')!r} differs from "
                            f"the R2 ledger section {ledger_row.get('section')!r}",
                            where,
                        )
                    )
                ledger_name = ledger_row.get("name")
                if _valid_text(ledger_name) and entry.get("originalDeclaration") != (
                    "PhotoLean.Relations." + ledger_name
                ):
                    findings.append(
                        Finding(
                            "migration.originalDeclarationMismatch",
                            f"originalDeclaration {entry.get('originalDeclaration')!r} does not "
                            f"match the R2 ledger name {ledger_name!r}",
                            where,
                        )
                    )

            section = entry.get("section")
            if not isinstance(section, int):
                findings.append(Finding("migration.entryStructure", "section must be an integer", where))
            elif isinstance(first, int) and isinstance(last, int) and not (first <= section <= last):
                findings.append(
                    Finding(
                        "migration.sectionMismatch",
                        f"section {section} is outside the fragment range {first}..{last}",
                        where,
                    )
                )

            r2_ledger = entry.get("r2Ledger")
            if not isinstance(r2_ledger, dict) or r2_ledger.get("disposition") != "certificate-required":
                findings.append(
                    Finding(
                        "migration.r2Ledger",
                        "r2Ledger.disposition must record certificate-required",
                        where,
                    )
                )
            original = entry.get("originalDeclaration")
            if not _valid_text(original):
                findings.append(
                    Finding("migration.sourceProvenance", "originalDeclaration must be a nonempty string", where)
                )
            elif relations_source is not None:
                short = str(original).split(".")[-1]
                if not re.search(
                    rf"(?m)^\s*(?:theorem|lemma|def)\s+{re.escape(short)}\b",
                    relations_source,
                ):
                    findings.append(
                        Finding(
                            "migration.originalDeclarationMissing",
                            f"{original} is not declared in {RELATIONS}",
                            where,
                        )
                    )

            premise_ids = _premise_ids(entry)
            for duplicate in _duplicates(premise_ids):
                findings.append(
                    Finding(
                        "migration.duplicatePremiseId",
                        f"premise ID {duplicate!r} occurs more than once",
                        where,
                    )
                )

            outcome = entry.get("outcome")
            if outcome == "certified":
                findings.extend(_validate_certified(entry, fragment, where))
            elif outcome == "reclassified":
                findings.extend(
                    _validate_reclassified(
                        entry,
                        fragment,
                        where,
                        all_rationales,
                    )
                )
            else:
                findings.append(
                    Finding(
                        "migration.outcome",
                        f"outcome must be certified or reclassified, got {outcome!r}",
                        where,
                    )
                )

    for declaration_id in queue_ids:
        if declaration_id not in all_seen:
            findings.append(
                Finding(
                    "migration.omittedDeclarationId",
                    f"{declaration_id} is certificate-required but appears in no fragment",
                    DISPOSITIONS,
                )
            )
        elif section_members.get(declaration_id, 0) > 1:
            pass  # already reported as a duplicate

    for declaration_id in all_seen:
        if declaration_id not in queue_set:
            if declaration_id in known:
                findings.append(
                    Finding(
                        "migration.nonQueueDeclarationId",
                        f"{declaration_id} is covered by a fragment but is not certificate-required",
                        all_seen[declaration_id],
                    )
                )
            else:
                # The unknown-ID finding above already names this row; do not
                # emit a second, less specific finding for the same row.
                pass

    return findings


def _validate_certified(
    entry: dict[str, Any], fragment: dict[str, Any], where: str
) -> list[Finding]:
    findings: list[Finding] = []
    certificate = entry.get("certificate")
    kind = entry.get("relationKind")
    if not _valid_text(certificate):
        findings.append(
            Finding("migration.missingCertificate", "certified row has no certificate name", where)
        )
    r2_ledger = entry.get("r2Ledger") if isinstance(entry.get("r2Ledger"), dict) else {}
    r2_role = r2_ledger.get("relationRole")
    if r2_role in NON_CERTIFIABLE_R2_ROLES:
        findings.append(
            Finding(
                "migration.nonDirectRoleCertified",
                f"certified row carries non-certifiable R2 relationRole {r2_role!r}; "
                "it must be reclassified",
                where,
            )
        )
    if kind not in RELATION_KINDS:
        findings.append(
            Finding(
                "migration.relationKind",
                f"relationKind must be one of the seven kinds, got {kind!r}",
                where,
            )
        )
        return findings

    expected_constructor = CERTIFICATE_CONSTRUCTOR_PREFIX + str(kind)
    if entry.get("certificateConstructor") != expected_constructor:
        findings.append(
            Finding(
                "migration.certificateConstructor",
                f"certificateConstructor must be {expected_constructor!r}",
                where,
            )
        )

    module = fragment.get("module")
    if entry.get("leanModule") != module:
        findings.append(
            Finding(
                "migration.leanModule",
                f"leanModule {entry.get('leanModule')!r} differs from fragment module {module!r}",
                where,
            )
        )

    for field in ("leanKindWitness", "leanPremiseWitness"):
        witness = entry.get(field)
        if not _valid_text(witness):
            findings.append(Finding("migration.witness", f"{field} must be a nonempty name", where))
        elif isinstance(module, str) and not witness.startswith(module + "."):
            findings.append(
                Finding(
                    "migration.witness",
                    f"{field} {witness!r} is not in the fragment module {module!r}",
                    where,
                )
            )

    statement = entry.get("statement")
    if not isinstance(statement, dict):
        findings.append(Finding("migration.statement", "statement must be an object", where))
    else:
        if statement.get("form") != kind:
            findings.append(
                Finding(
                    "migration.statementForm",
                    f"statement.form {statement.get('form')!r} differs from relationKind {kind!r}",
                    where,
                )
            )
        for side in ("left", "right"):
            ref = statement.get(side)
            if not isinstance(ref, dict) or not _valid_text(ref.get("theory")) or not _valid_text(
                ref.get("statementId")
            ):
                findings.append(
                    Finding(
                        "migration.statementSide",
                        f"statement.{side} must carry theory and statementId",
                        where,
                    )
                )

    provenance = entry.get("statementProvenance")
    references = provenance.get("references") if isinstance(provenance, dict) else None
    if not isinstance(references, list) or not references:
        findings.append(
            Finding(
                "migration.sourceProvenance",
                "statementProvenance.references must be a nonempty array",
                where,
            )
        )

    footprint = entry.get("axiomFootprint")
    if not isinstance(footprint, list) or not all(isinstance(item, str) for item in footprint):
        findings.append(
            Finding("migration.axiomFootprint", "axiomFootprint must be a string array", where)
        )
    else:
        disallowed = [item for item in footprint if item not in ALLOWED_AXIOMS]
        if disallowed:
            findings.append(
                Finding(
                    "migration.axiomFootprint",
                    f"disallowed axiom(s) declared: {', '.join(sorted(set(disallowed)))}",
                    where,
                )
            )
        for duplicate in _duplicates(footprint):
            findings.append(
                Finding(
                    "migration.axiomFootprint",
                    f"axiom {duplicate!r} is listed more than once",
                    where,
                )
            )

    if kind == "definitionalIdentity":
        witness = statement.get("definitionalWitness") if isinstance(statement, dict) else None
        if not isinstance(witness, dict):
            findings.append(
                Finding(
                    "migration.definitionalWitness",
                    "definitionalIdentity requires statement.definitionalWitness",
                    where,
                )
            )
        else:
            if witness.get("kind") != "DefEq.refl":
                findings.append(
                    Finding(
                        "migration.definitionalWitness",
                        "definitional witness kind must be DefEq.refl, not propositional equality",
                        where,
                    )
                )
            if not _valid_text(witness.get("functionWitness")):
                findings.append(
                    Finding(
                        "migration.definitionalWitness",
                        "definitional witness must name a fresh function-level witness",
                        where,
                    )
                )
            if not _valid_text(witness.get("sourceTheorem")) and not _valid_text(
                witness.get("pointwiseWitness")
            ):
                findings.append(
                    Finding(
                        "migration.definitionalWitness",
                        "definitional witness must expose a pointwise or source reuse witness",
                        where,
                    )
                )

    provenance_note = entry.get("compositionProvenance")
    composition = _composition_metadata(entry)
    if kind == "conditionalComposition":
        findings.extend(_validate_composition(composition, entry, where))
        if isinstance(provenance_note, dict) and provenance_note.get("typedParentComposition") is False:
            findings.append(
                Finding(
                    "migration.compositionMetadata",
                    "a conditionalComposition certificate cannot declare typedParentComposition=false",
                    where,
                )
            )
    else:
        if composition is not None:
            findings.append(
                Finding(
                    "migration.compositionMetadata",
                    "composition metadata is present on a non-composition certificate",
                    where,
                )
            )
        if isinstance(provenance_note, dict) and provenance_note.get("typedParentComposition") is True:
            findings.append(
                Finding(
                    "migration.compositionMetadata",
                    "compositionProvenance claims typedParentComposition=true, "
                    "but the certificate is not a conditionalComposition",
                    where,
                )
            )

    return findings


def _validate_composition(
    composition: dict[str, Any] | None, entry: dict[str, Any], where: str
) -> list[Finding]:
    findings: list[Finding] = []
    if composition is None:
        findings.append(
            Finding(
                "migration.compositionMetadata",
                "conditionalComposition requires a composition projection object",
                where,
            )
        )
        return findings
    parent_ids = composition.get("parentIDs")
    parent_kinds = composition.get("parentKinds")
    parent_premises = composition.get("parentPremiseIDs")
    bridge_ids = composition.get("bridgeIDs")
    discharge_ids = composition.get("dischargeIDs")
    mediating = composition.get("mediatingStatementID")
    form = composition.get("form")

    if not isinstance(parent_ids, list) or len(parent_ids) != 2 or not all(
        _valid_text(item) for item in parent_ids
    ):
        findings.append(
            Finding(
                "migration.compositionMetadata",
                "composition.parentIDs must hold exactly two nonempty parent IDs",
                where,
            )
        )
    if not isinstance(parent_kinds, list) or len(parent_kinds) != 2 or not all(
        item in COMPOSITION_PARENT_KINDS for item in parent_kinds
    ):
        findings.append(
            Finding(
                "migration.compositionMetadata",
                "composition.parentKinds must hold two implication/equivalence kinds",
                where,
            )
        )
    if (
        not isinstance(parent_premises, list)
        or len(parent_premises) != 2
        or not all(
            isinstance(group, list) and all(isinstance(item, str) for item in group)
            for group in parent_premises
        )
    ):
        findings.append(
            Finding(
                "migration.compositionMetadata",
                "composition.parentPremiseIDs must hold two string arrays",
                where,
            )
        )
    for field, value in (("bridgeIDs", bridge_ids), ("dischargeIDs", discharge_ids)):
        if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
            findings.append(
                Finding(
                    "migration.compositionMetadata",
                    f"composition.{field} must be a string array",
                    where,
                )
            )
    if not _valid_text(mediating):
        findings.append(
            Finding(
                "migration.compositionMetadata",
                "composition.mediatingStatementID must be a nonempty statement ID",
                where,
            )
        )
    if form not in {"implication", "equivalence"}:
        findings.append(
            Finding(
                "migration.compositionMetadata",
                "composition.form must be implication or equivalence",
                where,
            )
        )
    elif isinstance(parent_kinds, list) and len(parent_kinds) == 2:
        implied = (
            "equivalence"
            if parent_kinds[0] == "equivalence" and parent_kinds[1] == "equivalence"
            else "implication"
        )
        if form != implied:
            findings.append(
                Finding(
                    "migration.compositionForm",
                    f"declared form {form!r} is not the form implied by parentKinds {parent_kinds!r}",
                    where,
                )
            )
    return findings


def _validate_reclassified(
    entry: dict[str, Any],
    fragment: dict[str, Any],
    where: str,
    rationales: dict[str, str],
) -> list[Finding]:
    findings: list[Finding] = []
    if entry.get("certificate") is not None:
        findings.append(
            Finding(
                "migration.reclassifiedCertificate",
                "reclassified row must not carry a certificate",
                where,
            )
        )
    if entry.get("relationKind") is not None:
        findings.append(
            Finding(
                "migration.reclassifiedKind",
                "reclassified row must not carry a certified relationKind",
                where,
            )
        )

    category = entry.get("targetCategory")
    allowed = set(RELATION_KINDS) | _target_category_vocabulary(fragment)
    # A reclassification target is a disposition/role category, never a
    # certificate kind and never the migration queue's own disposition.
    if not _valid_text(category):
        findings.append(
            Finding("migration.reclassificationCategory", "targetCategory must be nonempty", where)
        )
    else:
        if category in RELATION_KINDS:
            findings.append(
                Finding(
                    "migration.reclassificationCategory",
                    f"targetCategory {category!r} is a certificate kind, not a migration category",
                    where,
                )
            )
        elif category in {"certificate-required", "pilot-certificate"}:
            findings.append(
                Finding(
                    "migration.reclassificationCategory",
                    f"targetCategory {category!r} is not a reclassification target",
                    where,
                )
            )
        elif category not in allowed:
            findings.append(
                Finding(
                    "migration.reclassificationCategory",
                    f"targetCategory {category!r} is outside the declared fragment vocabulary",
                    where,
                )
            )

    rationale = entry.get("rationale")
    if not _valid_text(rationale):
        findings.append(
            Finding("migration.reclassificationRationale", "rationale must be nonempty", where)
        )
    else:
        text = rationale.strip()
        if len(text) < MIN_RATIONALE_CHARS:
            findings.append(
                Finding(
                    "migration.reclassificationRationale",
                    f"rationale is only {len(text)} characters; at least {MIN_RATIONALE_CHARS} "
                    "are required to explain why no seven-kind certificate is honest",
                    where,
                )
            )
        elif _word_count(text) < MIN_RATIONALE_WORDS:
            findings.append(
                Finding(
                    "migration.reclassificationRationale",
                    f"rationale has only {_word_count(text)} words; at least "
                    f"{MIN_RATIONALE_WORDS} are required",
                    where,
                )
            )
        lowered = text.lower()
        for token in PLACEHOLDER_TOKENS:
            if token in lowered:
                findings.append(
                    Finding(
                        "migration.reclassificationRationale",
                        f"rationale contains placeholder token {token!r}",
                        where,
                    )
                )
                break
        previous = rationales.get(text)
        if previous is not None:
            findings.append(
                Finding(
                    "migration.reclassificationRationale",
                    f"rationale duplicates the rationale of {previous}",
                    where,
                )
            )
        else:
            rationales[text] = where

    blockers = entry.get("certificationBlockers")
    if not isinstance(blockers, list) or not blockers:
        findings.append(
            Finding(
                "migration.reclassificationBlockers",
                "certificationBlockers must be a nonempty array",
                where,
            )
        )
    else:
        for blocker in blockers:
            if not _valid_text(blocker):
                findings.append(
                    Finding(
                        "migration.reclassificationBlockers",
                        "every certification blocker must be a nonempty string",
                        where,
                    )
                )
                break

    evidence = entry.get("evidence")
    if not isinstance(evidence, dict):
        findings.append(
            Finding(
                "migration.reclassificationEvidence",
                "reclassified row needs an evidence object with a Lean re-export",
                where,
            )
        )
    else:
        if not _valid_text(evidence.get("leanName")):
            findings.append(
                Finding(
                    "migration.reclassificationEvidence",
                    "evidence.leanName must name the re-exported theorem",
                    where,
                )
            )
        if evidence.get("certificate") is not False:
            findings.append(
                Finding(
                    "migration.reclassificationEvidence",
                    "evidence.certificate must be false: a reclassification is not a certificate",
                    where,
                )
            )

    provenance = entry.get("statementProvenance")
    references = provenance.get("references") if isinstance(provenance, dict) else None
    if not _valid_text(entry.get("sourceLocator")) and (
        not isinstance(references, list) or not references
    ):
        findings.append(
            Finding(
                "migration.sourceProvenance",
                "reclassified row needs sourceLocator or statementProvenance.references",
                where,
            )
        )
    return findings


# --------------------------------------------------------------------- generation


def _lean_string(value: str) -> str:
    escaped = value.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
    return f'"{escaped}"'


def _lean_string_list(values: Iterable[str]) -> str:
    return "[" + ", ".join(_lean_string(value) for value in values) + "]"


def _lean_relkind(kind: str) -> str:
    return f"PhotoLean.RelationAudit.RelationKind.{kind}"


def _lean_composition_form(form: str) -> str:
    return f"PhotoLean.RelationAudit.CompositionForm.{form}"


def _ordered_entries(fragments: list[dict[str, Any]]) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    """Fragment order, then entry order: the fragment is the single source of truth."""
    return _entries(fragments)


def generate_lean_checks(fragments: list[dict[str, Any]]) -> tuple[str, list[dict[str, Any]]]:
    """Derive the generated Lean file from the fragments.

    Returns ``(source, specs)`` where each spec records one generated command and
    the declaration it exercises.  Nothing in this function is keyed by a
    hand-written certificate list.
    """
    entries = _ordered_entries(fragments)
    specs: list[dict[str, Any]] = []
    lines: list[str] = [
        "-- Generated by tools/relation_audit_migration.py from relation_audit/migration/*.json.",
        "-- Do not edit by hand; regenerate with `python3 tools/relation_audit_migration.py --generate`.",
        "-- This file elaborates the migration fragments' kind/premise/axiom claims and",
        "-- reclassification evidence. It is not a production registry and makes no coverage claim.",
        "",
        f"import {FULL_MODULE}",
        "",
    ]

    def emit(text: str, *, declaration: str, role: str, declaration_id: str) -> None:
        line = len(lines) + 1
        lines.append(text)
        specs.append(
            {
                "line": line,
                "checkId": f"{declaration_id}.{role}",
                "declarationId": declaration_id,
                "declaration": declaration,
                "role": role,
            }
        )

    certified = [(fragment, entry) for fragment, entry in entries if entry.get("outcome") == "certified"]
    reclassified = [
        (fragment, entry) for fragment, entry in entries if entry.get("outcome") == "reclassified"
    ]

    lines.extend(
        [
            "/-! ## Certified migration rows",
            "",
            "One `#check`, one kind pin, one premise-ID pin and one axiom probe per",
            "certified row. Definitional identities additionally check the fresh",
            "`DefEq.refl` witness and the delivered source/pointwise reuse witness.",
            "-/",
            "",
        ]
    )
    for _fragment, entry in certified:
        declaration_id = entry["declarationId"]
        certificate = entry["certificate"]
        kind = entry["relationKind"]
        premise_ids = _premise_ids(entry)
        emit(f"-- {declaration_id} ({kind})", declaration=certificate,
             role="comment", declaration_id=declaration_id)
        emit(f"#check {certificate}", declaration=certificate, role="exists",
             declaration_id=declaration_id)
        emit(
            f"example : {KIND_FUNCTION} {certificate} = {_lean_relkind(kind)} := rfl",
            declaration=certificate,
            role="kind",
            declaration_id=declaration_id,
        )
        emit(
            f"example : {PREMISE_FUNCTION} {certificate} = {_lean_string_list(premise_ids)} := rfl",
            declaration=certificate,
            role="premises",
            declaration_id=declaration_id,
        )
        emit(f"#print axioms {certificate}", declaration=certificate, role="axioms",
             declaration_id=declaration_id)

        statement = entry.get("statement") if isinstance(entry.get("statement"), dict) else {}
        witness = statement.get("definitionalWitness") if isinstance(statement, dict) else None
        if kind == "definitionalIdentity" and isinstance(witness, dict):
            for field, role in (
                ("functionWitness", "defeq"),
                ("pointwiseWitness", "pointwise"),
                ("sourceTheorem", "source"),
            ):
                name = witness.get(field)
                if not _valid_text(name):
                    continue
                emit(f"#check {name}", declaration=name, role=role, declaration_id=declaration_id)
                emit(f"#print axioms {name}", declaration=name, role=f"{role}_axioms",
                     declaration_id=declaration_id)

        composition = _composition_metadata(entry)
        if kind == "conditionalComposition" and composition is not None:
            parent_ids = composition["parentIDs"]
            parent_kinds = composition["parentKinds"]
            parent_premises = composition["parentPremiseIDs"]
            bridge_ids = composition["bridgeIDs"]
            discharge_ids = composition["dischargeIDs"]
            mediating = composition["mediatingStatementID"]
            form = composition["form"]
            emit(
                f"example : PhotoLean.RelationAudit.certificateParentIDs {certificate} = "
                f"{_lean_string_list(parent_ids)} := rfl",
                declaration=certificate,
                role="composition_parents",
                declaration_id=declaration_id,
            )
            emit(
                f"example : PhotoLean.RelationAudit.certificateParentKinds {certificate} = "
                f"[{', '.join(_lean_relkind(item) for item in parent_kinds)}] := rfl",
                declaration=certificate,
                role="composition_parent_kinds",
                declaration_id=declaration_id,
            )
            emit(
                f"example : PhotoLean.RelationAudit.certificateParentPremiseIDs {certificate} = "
                f"[{', '.join(_lean_string_list(group) for group in parent_premises)}] := rfl",
                declaration=certificate,
                role="composition_parent_premises",
                declaration_id=declaration_id,
            )
            emit(
                f"example : PhotoLean.RelationAudit.certificateBridgeIDs {certificate} = "
                f"{_lean_string_list(bridge_ids)} := rfl",
                declaration=certificate,
                role="composition_bridges",
                declaration_id=declaration_id,
            )
            emit(
                f"example : PhotoLean.RelationAudit.certificateDischargeIDs {certificate} = "
                f"{_lean_string_list(discharge_ids)} := rfl",
                declaration=certificate,
                role="composition_discharges",
                declaration_id=declaration_id,
            )
            emit(
                f"example : (PhotoLean.RelationAudit.certificateMediating? {certificate}).map "
                f"(fun s => s.statementId) = some {_lean_string(mediating)} := rfl",
                declaration=certificate,
                role="composition_mediating",
                declaration_id=declaration_id,
            )
            emit(
                f"example : PhotoLean.RelationAudit.certificateCompositionForm? {certificate} = "
                f"some {_lean_composition_form(form)} := rfl",
                declaration=certificate,
                role="composition_form",
                declaration_id=declaration_id,
            )

    lines.extend(
        [
            "",
            "/-! ## Reclassification evidence",
            "",
            "Each reclassified row has a Lean re-export that elaborates. These are",
            "deliberately not `Certificate` values; the `#check` only proves that the",
            "evidence named by the fragment exists and its axiom footprint is allowed.",
            "-/",
            "",
        ]
    )
    for _fragment, entry in reclassified:
        declaration_id = entry["declarationId"]
        category = entry.get("targetCategory")
        evidence = entry.get("evidence") if isinstance(entry.get("evidence"), dict) else {}
        name = evidence.get("leanName")
        emit(f"-- {declaration_id} -> {category}", declaration=str(name or declaration_id),
             role="comment", declaration_id=declaration_id)
        if _valid_text(name):
            emit(f"#check {name}", declaration=name, role="evidence", declaration_id=declaration_id)
            emit(f"#print axioms {name}", declaration=name, role="evidence_axioms",
                 declaration_id=declaration_id)

    composition_count = sum(
        1 for _fragment, entry in certified if entry.get("relationKind") == "conditionalComposition"
    )
    lines.extend(
        [
            "",
            "/-! ## Composition projections",
            "",
            (
                f"Conditional-composition certificates in the R3 fragments: {composition_count}."
            ),
            (
                "No composition projection is emitted because no fragment row uses the "
                "`conditionalComposition` constructor; the generator still supports the "
                "canonical parent/premise/mediator/form projections for a future composition row."
            ),
            "-/",
            "",
        ]
    )
    return "\n".join(lines), specs


# ------------------------------------------------------------------------- report


def build_report(
    fragments: list[dict[str, Any]],
    dispositions: dict[str, Any],
    root: str,
    lean_source: str,
    specs: list[dict[str, Any]],
) -> dict[str, Any]:
    queue = queue_entries(dispositions)
    queue_ids = [entry["declarationId"] for entry in queue]
    entries = _ordered_entries(fragments)

    kind_counts = {kind: 0 for kind in RELATION_KINDS}
    target_counts: dict[str, int] = {}
    certificates: list[dict[str, Any]] = []
    reclassifications: list[dict[str, Any]] = []
    per_fragment: list[dict[str, Any]] = []

    for fragment in fragments:
        fragment_entries = fragment.get("entries", [])
        fragment_kinds = {kind: 0 for kind in RELATION_KINDS}
        fragment_targets: dict[str, int] = {}
        certified_count = 0
        reclassified_count = 0
        for entry in fragment_entries:
            if entry.get("outcome") == "certified":
                certified_count += 1
                kind = entry.get("relationKind")
                if kind in fragment_kinds:
                    fragment_kinds[kind] += 1
                    kind_counts[kind] += 1
            elif entry.get("outcome") == "reclassified":
                reclassified_count += 1
                category = entry.get("targetCategory")
                if isinstance(category, str):
                    fragment_targets[category] = fragment_targets.get(category, 0) + 1
                    target_counts[category] = target_counts.get(category, 0) + 1
        lean_source_path = fragment.get("leanSource")
        actual_hash = None
        if isinstance(lean_source_path, str) and os.path.isfile(_path(root, lean_source_path)):
            actual_hash = sha256_file(_path(root, lean_source_path))
        per_fragment.append(
            {
                "name": fragment.get("_fragmentName"),
                "path": fragment.get("_fragmentPath"),
                "module": fragment.get("module"),
                "sectionRange": fragment.get("sectionRange"),
                "declarations": len(fragment_entries),
                "certified": certified_count,
                "reclassified": reclassified_count,
                "kindCounts": {key: value for key, value in fragment_kinds.items() if value},
                "targetCategoryCounts": fragment_targets,
                "leanSource": lean_source_path,
                "leanSourceSha256": actual_hash,
                "declaredLeanSourceSha256": fragment.get("leanSourceSha256"),
                "hashMatches": (
                    fragment.get("leanSourceSha256") == actual_hash
                    if fragment.get("leanSourceSha256") is not None
                    else None
                ),
            }
        )

    for fragment, entry in entries:
        if entry.get("outcome") == "certified":
            certificates.append(
                {
                    "declarationId": entry.get("declarationId"),
                    "originalDeclaration": entry.get("originalDeclaration"),
                    "section": entry.get("section"),
                    "module": entry.get("leanModule"),
                    "certificate": entry.get("certificate"),
                    "relationKind": entry.get("relationKind"),
                    "premiseIDs": _premise_ids(entry),
                    "axiomFootprint": entry.get("axiomFootprint", []),
                    "leanKindWitness": entry.get("leanKindWitness"),
                    "leanPremiseWitness": entry.get("leanPremiseWitness"),
                }
            )
        elif entry.get("outcome") == "reclassified":
            evidence = entry.get("evidence") if isinstance(entry.get("evidence"), dict) else {}
            reclassifications.append(
                {
                    "declarationId": entry.get("declarationId"),
                    "originalDeclaration": entry.get("originalDeclaration"),
                    "section": entry.get("section"),
                    "module": fragment.get("module"),
                    "targetCategory": entry.get("targetCategory"),
                    "certificationBlockers": entry.get("certificationBlockers", []),
                    "rationale": entry.get("rationale"),
                    "evidenceLeanName": evidence.get("leanName"),
                }
            )

    kinds = {kind: count for kind, count in kind_counts.items() if count}
    total_certified = sum(1 for _fragment, entry in entries if entry.get("outcome") == "certified")
    total_reclassified = sum(
        1 for _fragment, entry in entries if entry.get("outcome") == "reclassified"
    )
    report: dict[str, Any] = {
        "schemaVersion": SCHEMA_VERSION,
        "artifactKind": "relation-migration-report",
        "status": "FRAGMENTS_VALIDATED",
        "scope": "migration-fragment-integration",
        "sourceOfTruth": {
            "dispositions": DISPOSITIONS,
            "fragments": [path for _name, path in FRAGMENTS],
            "relationSource": RELATIONS,
            "generator": "tools/relation_audit/migration.py",
            "leanImport": FULL_MODULE,
            "note": "Every certificate name below is read from the fragments; there is no second list.",
        },
        "queue": {
            "source": "dispositions.json entries with disposition == 'certificate-required'",
            "expectedCount": len(queue_ids),
            "coveredCount": len(entries),
            "uniqueDeclarationIds": len({entry.get("declarationId") for _f, entry in entries}),
            "declarationIds": [entry.get("declarationId") for _f, entry in entries],
        },
        "counts": {
            "fragments": len(fragments),
            "declarations": len(entries),
            "certified": total_certified,
            "reclassified": total_reclassified,
            "kindCounts": kinds,
            "targetCategoryCounts": dict(sorted(target_counts.items())),
            "conditionalCompositionCertificates": kind_counts.get("conditionalComposition", 0),
            "definitionalIdentityCertificates": kind_counts.get("definitionalIdentity", 0),
            "reclassifiedShare": (
                round(total_reclassified / len(entries), 4) if entries else 0.0
            ),
        },
        "fragments": per_fragment,
        "certificates": certificates,
        "reclassifications": reclassifications,
        "generatedChecks": {
            "path": LEAN_OUT,
            "sha256": sha256_text(lean_source),
            "commandCount": len([spec for spec in specs if spec["role"] != "comment"]),
            "specs": specs,
            "import": FULL_MODULE,
            "compositionProjections": (
                "emitted per composition row when relationKind == conditionalComposition"
            ),
        },
        "gates": {
            "queueCoverage": "PASS",
            "certificateShape": "PASS",
            "reclassificationShape": "PASS",
            "generatedLeanSource": "GENERATED",
            "leanElaboration": "SEPARATE_VERIFICATION_COMMAND",
            "leanVerificationCommand": (
                "python3 tools/relation_audit_migration.py --check --lean"
            ),
            "axiomFootprints": "DECLARED_IN_FRAGMENTS_AND_CHECKED_BY_LEAN_COMMAND",
        },
        "nonClaims": NON_CLAIMS,
    }
    return report


def render_markdown(report: dict[str, Any]) -> str:
    counts = report["counts"]
    lines = [
        "# Relation-Audit R3 Migration Fragment Integration Report",
        "",
        "Status: **fragments validated** — this is not a production registry and not an",
        "audit verdict. It covers exactly the 41 R2 certificate-required declarations.",
        "",
        "## Counts",
        "",
        "| item | value |",
        "|---|---|",
        f"| fragments | {counts['fragments']} |",
        f"| queue declarations | {report['queue']['expectedCount']} |",
        f"| covered declarations | {report['queue']['coveredCount']} |",
        f"| certified | {counts['certified']} |",
        f"| reclassified | {counts['reclassified']} |",
        f"| conditionalComposition certificates | {counts['conditionalCompositionCertificates']} |",
        "",
        "## Certified by kind",
        "",
        "| kind | declarations |",
        "|---|---|",
    ]
    for kind, value in counts["kindCounts"].items():
        lines.append(f"| `{kind}` | {value} |")
    lines += ["", "## Reclassification targets", "", "| target category | declarations |", "|---|---|"]
    for category, value in counts["targetCategoryCounts"].items():
        lines.append(f"| `{category}` | {value} |")
    lines += ["", "## Fragments", "", "| fragment | module | declarations | certified | reclassified |", "|---|---|---|---|---|"]
    for fragment in report["fragments"]:
        lines.append(
            f"| `{fragment['name']}` | `{fragment['module']}` | {fragment['declarations']} | "
            f"{fragment['certified']} | {fragment['reclassified']} |"
        )
    lines += ["", "## Certified rows", "", "| declaration | kind | premises | certificate |", "|---|---|---|---|"]
    for certificate in report["certificates"]:
        premises = ", ".join(f"`{item}`" for item in certificate["premiseIDs"]) or "—"
        lines.append(
            f"| `{certificate['declarationId']}` | `{certificate['relationKind']}` | "
            f"{premises} | `{certificate['certificate']}` |"
        )
    lines += ["", "## Reclassified rows", ""]
    lines.append("Every row below is evidence-only and is **not** a certified relation.")
    lines += ["", "| declaration | target | blockers | evidence |", "|---|---|---|---|"]
    for row in report["reclassifications"]:
        blockers = ", ".join(f"`{item}`" for item in row["certificationBlockers"]) or "—"
        lines.append(
            f"| `{row['declarationId']}` | `{row['targetCategory']}` | {blockers} | "
            f"`{row['evidenceLeanName']}` |"
        )
    lines += ["", "## Generated checks", ""]
    generated = report["generatedChecks"]
    lines.append(
        f"- source: `{generated['path']}` (`{generated['sha256'][:12]}…`), "
        f"{generated['commandCount']} commands, imports `{generated['import']}`"
    )
    lines += ["", "## Non-claims", ""]
    for item in report["nonClaims"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


# ------------------------------------------------------------------------- drift


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
                f"{relative} is stale; rerun --generate and inspect the fragment drift "
                "before accepting it",
                relative,
            )
        ]
    return []


# ----------------------------------------------------------------------- lean run


_AXIOM_BLOCK = re.compile(
    r"^'(?P<decl>.+?)' (?:does not depend on any axioms"
    r"|depends on axioms: \[(?P<axioms>[^\]]*)\])",
    re.DOTALL | re.MULTILINE,
)


def parse_axiom_footprints(output: str) -> dict[str, set[str]]:
    """Parse every `#print axioms` block, tolerating Format line wrapping."""
    footprints: dict[str, set[str]] = {}
    for match in _AXIOM_BLOCK.finditer(output):
        name = match.group("decl").strip()
        raw = match.group("axioms")
        if raw is None:
            footprints[name] = set()
        else:
            footprints[name] = {
                item.strip() for item in raw.replace("\n", " ").split(",") if item.strip()
            }
    return footprints


def expected_axiom_declarations(
    fragments: list[dict[str, Any]],
) -> dict[str, set[str] | None]:
    """The declarations whose footprints the generated file prints.

    A certificate is strict: its observed footprint must equal the fragment's
    declared footprint. Evidence and definitional witnesses are checked only
    against the global allow-list (`None` means "any subset of ALLOWED_AXIOMS").
    """
    expected: dict[str, set[str] | None] = {}
    for _fragment, entry in _ordered_entries(fragments):
        if entry.get("outcome") == "certified":
            certificate = entry.get("certificate")
            footprint = entry.get("axiomFootprint")
            if _valid_text(certificate):
                expected[certificate] = set(footprint if isinstance(footprint, list) else [])
                statement = entry.get("statement") if isinstance(entry.get("statement"), dict) else {}
                witness = statement.get("definitionalWitness") if isinstance(statement, dict) else None
                if isinstance(witness, dict):
                    for field in ("functionWitness", "pointwiseWitness", "sourceTheorem"):
                        name = witness.get(field)
                        if _valid_text(name):
                            expected.setdefault(name, None)
        elif entry.get("outcome") == "reclassified":
            evidence = entry.get("evidence") if isinstance(entry.get("evidence"), dict) else {}
            name = evidence.get("leanName")
            if _valid_text(name):
                expected.setdefault(name, None)
    return expected


def run_lean_checks(
    root: str,
    lean_path: str,
    fragments: list[dict[str, Any]],
    *,
    timeout: float = 900.0,
) -> tuple[list[Finding], dict[str, Any]]:
    """Build the Full module, elaborate the generated file, and check footprints."""
    findings: list[Finding] = []
    lake = _path(root, os.path.join("proofs", "scripts", "lake"))
    if not os.path.isfile(lake) or not os.access(lake, os.X_OK):
        return [Finding("lean.launcher", f"missing or non-executable {lake}", lean_path)], {}

    build = subprocess.run(
        [lake, "build", FULL_MODULE],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    if build.returncode != 0:
        tail = "\n".join((build.stdout or "").strip().splitlines()[-20:])
        return (
            [Finding("lean.build", f"lake build {FULL_MODULE} failed: {tail}", lean_path)],
            {"buildExit": build.returncode},
        )

    run = subprocess.run(
        [lake, "env", "lean", lean_path],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    output = run.stdout or ""
    if run.returncode != 0:
        tail = "\n".join(output.strip().splitlines()[-40:])
        return (
            [
                Finding(
                    "lean.elaboration",
                    f"generated Lean checks failed to elaborate (exit {run.returncode}): {tail}",
                    lean_path,
                )
            ],
            {"buildExit": build.returncode, "leanExit": run.returncode},
        )

    observed = parse_axiom_footprints(output)
    expected = expected_axiom_declarations(fragments)
    for declaration, allowed in expected.items():
        if declaration not in observed:
            findings.append(
                Finding(
                    "lean.axiomsMissing",
                    f"no #print axioms block found for {declaration}",
                    lean_path,
                )
            )
            continue
        footprint = observed[declaration]
        disallowed = footprint - set(ALLOWED_AXIOMS)
        if disallowed:
            findings.append(
                Finding(
                    "lean.axiomsDisallowed",
                    f"{declaration} depends on disallowed axiom(s): "
                    f"{', '.join(sorted(disallowed))}",
                    lean_path,
                )
            )
        elif allowed is not None and footprint != allowed:
            findings.append(
                Finding(
                    "lean.axiomsDrift",
                    f"{declaration} footprint is {sorted(footprint)!r}, fragment declares "
                    f"{sorted(allowed)!r}",
                    lean_path,
                )
            )
    return findings, {
        "buildExit": build.returncode,
        "leanExit": run.returncode,
        "declarationsChecked": len(expected),
        "axiomBlocksObserved": len(observed),
    }


# --------------------------------------------------------------------------- CLI


def generate(root: str) -> int:
    fragments = load_fragments(root)
    dispositions = load_dispositions(root)
    relations_source = None
    relations_path = _path(root, RELATIONS)
    if os.path.isfile(relations_path):
        with open(relations_path, encoding="utf-8") as handle:
            relations_source = handle.read()
    findings = validate_fragments(fragments, dispositions, relations_source=relations_source)
    findings.extend(_validate_lean_hashes(root, fragments))
    if findings:
        for finding in findings:
            print(finding)
        print(f"migration generation refused: {len(findings)} finding(s)")
        return 1

    lean_source, specs = generate_lean_checks(fragments)
    report = build_report(fragments, dispositions, root, lean_source, specs)
    markdown = render_markdown(report)
    outputs = [
        (REPORT_JSON, json_text(report)),
        (REPORT_MD, markdown),
        (LEAN_OUT, lean_source),
    ]
    for relative, text in outputs:
        path = _path(root, relative)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(text)
    print(
        "migration generated: "
        f"{report['queue']['coveredCount']} declarations, "
        f"{report['counts']['certified']} certified, "
        f"{report['counts']['reclassified']} reclassified, "
        f"{report['counts']['conditionalCompositionCertificates']} conditionalComposition"
    )
    for relative, _text in outputs:
        print(f"  wrote {relative}")
    print("scope: migration fragments only; no production registry and no coverage claim")
    return 0


def _validate_lean_hashes(root: str, fragments: list[dict[str, Any]]) -> list[Finding]:
    findings: list[Finding] = []
    for fragment in fragments:
        path = fragment.get("leanSource")
        declared = fragment.get("leanSourceSha256")
        if not _valid_text(path):
            findings.append(
                Finding(
                    "migration.leanSource",
                    "fragment does not name its Lean source module",
                    str(fragment.get("_fragmentPath")),
                )
            )
            continue
        absolute = _path(root, path)
        if not os.path.isfile(absolute):
            findings.append(
                Finding("migration.leanSource", f"missing Lean source {path}", str(fragment.get("_fragmentPath")))
            )
            continue
        if declared is not None:
            actual = sha256_file(absolute)
            if actual != declared:
                findings.append(
                    Finding(
                        "migration.leanSourceHash",
                        f"{path} hash {actual} no longer matches the fragment's declared {declared}",
                        str(fragment.get("_fragmentPath")),
                    )
                )
    return findings


def check(root: str, *, lean: bool = False) -> int:
    fragments = load_fragments(root)
    dispositions = load_dispositions(root)
    relations_source = None
    relations_path = _path(root, RELATIONS)
    if os.path.isfile(relations_path):
        with open(relations_path, encoding="utf-8") as handle:
            relations_source = handle.read()
    findings = validate_fragments(fragments, dispositions, relations_source=relations_source)
    findings.extend(_validate_lean_hashes(root, fragments))

    lean_source, specs = generate_lean_checks(fragments)
    report = build_report(fragments, dispositions, root, lean_source, specs)
    findings.extend(_compare_file(root, REPORT_JSON, json_text(report)))
    findings.extend(_compare_file(root, REPORT_MD, render_markdown(report)))
    findings.extend(_compare_file(root, LEAN_OUT, lean_source))

    lean_result: dict[str, Any] = {}
    if lean and not findings:
        lean_findings, lean_result = run_lean_checks(root, _path(root, LEAN_OUT), fragments)
        findings.extend(lean_findings)

    if findings:
        for finding in findings:
            print(finding)
        print(f"migration check: {len(findings)} finding(s)")
        return 1

    print(
        "migration check: OK "
        f"({report['queue']['coveredCount']}/{report['queue']['expectedCount']} queue IDs, "
        f"{report['counts']['certified']} certified, "
        f"{report['counts']['reclassified']} reclassified, "
        f"{report['counts']['conditionalCompositionCertificates']} conditionalComposition; "
        "fragments only, not an audit verdict)"
    )
    if lean:
        print(
            "lean checks: OK "
            f"({lean_result.get('declarationsChecked', 0)} footprints, "
            f"build exit {lean_result.get('buildExit')}, lean exit {lean_result.get('leanExit')})"
        )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="relation_audit_migration.py",
        description=(
            "Fail-closed checker and Lean-check generator for the R3 migration fragments. "
            "Every certificate name is derived from relation_audit/migration/*.json."
        ),
    )
    parser.add_argument("--generate", action="store_true", help="write the report and generated Lean checks")
    parser.add_argument("--check", action="store_true", help="check fragments and checked-in artifact drift (default)")
    parser.add_argument("--lean", action="store_true", help="also build Full and elaborate the generated checks")
    parser.add_argument("--repo-root", default=None, help="repository root (default: the checkout containing this tool)")
    parser.add_argument("--quiet", action="store_true", help="only print the final line")
    args = parser.parse_args(argv)
    if args.generate and args.check:
        parser.error("--generate and --check are mutually exclusive")
    try:
        root = args.repo_root or repo_root(__file__)
        if args.generate:
            if args.lean:
                parser.error("--lean is only meaningful with --check")
            return generate(root)
        if args.quiet and not args.lean:
            import contextlib
            import io

            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                code = check(root, lean=False)
            lines = buffer.getvalue().strip().splitlines()
            print(lines[-1] if lines else ("migration check: OK" if code == 0 else "migration check: FAILED"))
            return code
        return check(root, lean=args.lean)
    except MigrationError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    except (OSError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())

#!/usr/bin/env python3
"""Regenerate the relation-audit test fixtures.

The fixtures pin the source snapshot recorded in relation-genealogy/WORKSPACE.md
(``7ad25a5f03a88acc3af03f65149cf2ac102e7dac``).  Statement artifact hashes are
computed with ``git show <snapshot>:<path>`` so the fixtures stay valid when the
working tree advances: a historical snapshot remains a valid pinned provenance
record as long as its toolchain, schema and artifact hashes still match.

Run from the repository root:

    python3 tests/relation_audit/fixtures/generate.py

This writes:

    fixtures/manifest_pilot.json      valid pilot: all seven kinds + statuses
    fixtures/manifest_full.json       valid full: 136/136 pair registry
    fixtures/invalid/*.json           one-defect manifests used by the tests
"""

from __future__ import annotations

import copy
import hashlib
import json
import os
import subprocess
import sys


SOURCE_SNAPSHOT = "7ad25a5f03a88acc3af03f65149cf2ac102e7dac"
SCHEMA_VERSION = "1.2.0"

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))

# (theory, statement id, artifact, declaration/context note)
THEORIES = [
    ("Marcus", "marcus.barrier", "PhotoLean/Marcus/Barrier.lean",
     "Marcus barrier and reorganization-energy statement surface"),
    ("Hammond", "hammond.gap", "PhotoLean/Hammond/Basic.lean",
     "Hammond forward/reverse gap statement surface"),
    ("BEP", "bep.transfer", "PhotoLean/BEP/Basic.lean",
     "Bell-Evans-Polanyi transfer coefficient statement surface"),
    ("Kasha", "kasha.rate", "PhotoLean/Kasha/Basic.lean",
     "Kasha internal-conversion rate statement surface"),
    ("Sabatier", "sabatier.volcano", "PhotoLean/Sabatier/Basic.lean",
     "Sabatier volcano activity statement surface"),
    ("Goldschmidt", "goldschmidt.tolerance", "PhotoLean/Goldschmidt/Basic.lean",
     "Goldschmidt tolerance-factor statement surface"),
    ("SymmetryFactor", "symmetry.factor", "PhotoLean/SymmetryFactor/Basic.lean",
     "symmetry-factor statement surface"),
    ("KashaVavilov", "kashavavilov.shift", "PhotoLean/KashaVavilov/Basic.lean",
     "Kasha-Vavilov shift statement surface"),
    ("SternVolmer", "sternvolmer.intensity", "PhotoLean/SternVolmer/Basic.lean",
     "Stern-Volmer intensity statement surface"),
    ("QuantumYield", "quantumyield.yield", "PhotoLean/QuantumYield/Basic.lean",
     "quantum-yield statement surface"),
    ("FluorPhos", "fluorphos.yield", "PhotoLean/FluorPhos/Basic.lean",
     "fluorophore phosphorescence statement surface"),
    ("EnergyGapLaw", "energygap.law", "PhotoLean/EnergyGapLaw/Basic.lean",
     "energy-gap-law statement surface"),
    ("StokesShift", "stokes.shift", "PhotoLean/StokesShift/Basic.lean",
     "Stokes-shift statement surface"),
    ("ICvsISC", "ic.isc", "PhotoLean/ICvsISC/Basic.lean",
     "internal-conversion vs intersystem-crossing statement surface"),
    ("Forster", "forster.transfer", "PhotoLean/Forster/Basic.lean",
     "Forster resonance transfer statement surface"),
    ("Einstein", "einstein.rate", "PhotoLean/Einstein/Basic.lean",
     "Einstein A/B coefficient statement surface"),
    ("RACI", "raci.branching", "PhotoLean/RACI/Accessibility.lean",
     "RACI branching statement surface"),
]

STATEMENT_BY_THEORY = {theory: statement for theory, statement, _, _ in THEORIES}
STATEMENT_ARTIFACT = {statement: artifact for _, statement, artifact, _ in THEORIES}


def git_show(path: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", REPO_ROOT, "show", f"{SOURCE_SNAPSHOT}:{path}"],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        raise SystemExit(
            f"cannot read {path} at source snapshot {SOURCE_SNAPSHOT}: "
            f"{completed.stderr.decode(errors='replace').strip()}")
    return completed.stdout


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def schema_hash() -> str:
    with open(os.path.join(HERE, "schema.json"), "rb") as handle:
        return sha256(handle.read())


def toolchain() -> str:
    with open(os.path.join(REPO_ROOT, "lean-toolchain"), encoding="utf-8") as handle:
        return handle.read().strip()


def provenance(kind: str, artifact: str, locator: str, rationale: str | None = None) -> dict:
    data = {
        "kind": kind,
        "references": [{"artifact": artifact, "locator": locator}],
    }
    if rationale is not None:
        data["rationale"] = rationale
    return data


def statement_provenance(artifact: str, note: str) -> dict:
    return provenance("source", artifact, "statement surface", note)


def make_snapshot(statement_hashes: dict[str, str]) -> dict:
    return {
        "id": "snap-source-7ad25a5",
        "treeSha": SOURCE_SNAPSHOT,
        "toolchain": toolchain(),
        "schemaSha256": schema_hash(),
        "artifacts": dict(sorted(statement_hashes.items())),
    }


def make_statements() -> tuple[list[dict], dict[str, str]]:
    statements = []
    hashes: dict[str, str] = {}
    for theory, statement_id, artifact, note in THEORIES:
        digest = sha256(git_show(artifact))
        hashes[artifact] = digest
        statements.append({
            "id": statement_id,
            "theory": theory,
            "artifact": artifact,
            "version": "1.0.0",
            "sha256": digest,
            "context": f"{theory} statement context at source snapshot 7ad25a5",
            "declaration": f"PhotoLean.{theory}",
            "provenance": statement_provenance(artifact, note),
        })
    return statements, hashes


def make_scopes() -> list[dict]:
    return [
        {
            "id": "global",
            "kind": "global",
            "description": "Unrestricted comparison context over the shared semantic domain.",
            "theories": [theory for theory, _, _, _ in THEORIES],
            "provenance": provenance(
                "source", "docs/RELATION-AUDIT-CONTRACT.md", "section 4",
                "The contract's shared-context Delta is unrestricted in the pilot."),
        },
        {
            "id": "bep-kasha",
            "kind": "restricted",
            "description": "Restricted scope covering only the BEP and Kasha statements.",
            "theories": ["BEP", "Kasha"],
            "provenance": provenance(
                "source", "docs/RELATION-AUDIT-CONTRACT.md", "section 4",
                "A restricted context used by the scope-mutation fixture."),
        },
        {
            "id": "outside-genealogy",
            "kind": "outOfScope",
            "description": "Comparisons excluded from the genealogy universe by scope agreement.",
            "theories": ["RACI", "Einstein"],
            "provenance": provenance(
                "source", "docs/RELATION-AUDIT-CONTRACT.md", "section 7",
                "Scoped exclusion, registered before any relational claim."),
        },
    ]


def make_query(query_id: str, source_statement: str, target_statement: str,
               context: str) -> dict:
    return {
        "id": query_id,
        "source": source_statement,
        "target": target_statement,
        "context": context,
        "provenance": provenance(
            "source", "theories/RELATIONS.md", "relation ledger",
            "Registered query between two stable statement ids."),
    }


def semantics_for(translation: str, **extra) -> dict:
    data = {
        "context": "shared semantic domain Delta over the declared translation.",
        "translations": {
            "left": "RelationAuditFixture.translateLeft",
            "right": "RelationAuditFixture.translateRight",
        },
        "premisePredicate": "RelationAuditFixture.premisePredicate",
        "translation": translation,
    }
    data.update(extra)
    return data


def make_certificate(cert_id: str, kind: str, lean: str, *, premises=None,
                     semantics=None, axiom_footprint=None) -> dict:
    data = {
        "id": cert_id,
        "kind": kind,
        "module": "RelationAuditFixture",
        "lean": lean,
        "kindFunction": "RelationAuditFixture.certificateKind",
        "constructor": f"RelationAuditFixture.CertificateKind.{kind}",
        "premises": premises or [],
        "semantics": semantics if semantics is not None else semantics_for(
            "Identity translation on the shared context."),
        "axiomFootprint": axiom_footprint if axiom_footprint is not None else [],
    }
    return data


def premise(premise_id: str, statement: str, *, explicit: bool = False,
            signature_name: str | None = None,
            signature_declaration: str | None = None) -> dict:
    data = {"id": premise_id, "statement": statement}
    if explicit:
        data["explicit"] = True
    if signature_name:
        data["signatureName"] = signature_name
    if signature_declaration:
        data["signatureDeclaration"] = signature_declaration
    return data


def record(record_id: str, query_id: str, version: str, status: str, *,
           scope: str = "global", snapshot: str = "snap-source-7ad25a5",
           relation_kind: str | None = None, certificate: str | None = None,
           rationale: str | None = None, candidate: str | None = None,
           premises=None, badges=None, composition=None, dependencies=None) -> dict:
    data = {
        "id": record_id,
        "queryId": query_id,
        "statementVersion": version,
        "scope": scope,
        "status": status,
        "snapshot": snapshot,
        "provenance": provenance(
            "source" if status == "certified" else "manual",
            "theories/RELATIONS.md", "relation ledger",
            rationale if status != "certified" else
            "Certificate registered from the checked Lean module."),
    }
    if relation_kind is not None:
        data["relationKind"] = relation_kind
    if certificate is not None:
        data["certificate"] = certificate
    if rationale is not None:
        data["rationale"] = rationale
    if candidate is not None:
        data["candidate"] = candidate
    if status == "certified":
        data["premises"] = premises if premises is not None else []
        data["badges"] = badges if badges is not None else {}
    else:
        if premises is not None:
            data["premises"] = premises
        if badges is not None:
            data["badges"] = badges
    if composition is not None:
        data["composition"] = composition
    if dependencies is not None:
        data["dependencies"] = dependencies
    return data


def make_pilot() -> dict:
    statements, hashes = make_statements()
    scopes = make_scopes()
    snapshot = make_snapshot(hashes)

    queries = [
        make_query("q-def", "marcus.barrier", "hammond.gap",
                   "definitional pin between Marcus barrier and Hammond gap"),
        make_query("q-impl", "bep.transfer", "hammond.gap",
                   "one-way entailment from BEP transfer to Hammond gap"),
        make_query("q-equiv", "symmetry.factor", "bep.transfer",
                   "A1 equivalence between the symmetry factor and the transfer coefficient"),
        make_query("q-comp", "kasha.rate", "marcus.barrier",
                   "Kasha-Marcus conditional composition through the hic bridge"),
        make_query("q-obs", "sternvolmer.intensity", "stokes.shift",
                   "intensity-channel observational equivalence"),
        make_query("q-dist", "sternvolmer.intensity", "ic.isc",
                   "joint-channel distinguishability"),
        make_query("q-refu", "hammond.gap", "marcus.barrier",
                   "explicit counterexample refuting an unconditional implication"),
        make_query("q-unres", "fluorphos.yield", "energygap.law",
                   "undelivered candidate relation"),
        make_query("q-not", "goldschmidt.tolerance", "marcus.barrier",
                   "scoped no-edge registration"),
        make_query("q-out", "raci.branching", "einstein.rate",
                   "scope agreement excluding the comparison"),
    ]

    p_adj = premise(
        "p-adj", "The step is adiabatic in the declared reaction window.",
        explicit=True, signature_name="hAdj",
        signature_declaration="RelationAuditFixture.lemmaImpl")
    p_pos = premise(
        "p-pos", "The reorganization energy is positive.",
        explicit=True, signature_name="hPos",
        signature_declaration="RelationAuditFixture.lemmaEquiv")

    certificates = [
        make_certificate(
            "cert-def", "definitionalIdentity",
            "RelationAuditFixture.certDefId",
            semantics=semantics_for(
                "Marcus barrier := Hammond forward gap (definitional alias).",
                rflWitness="RelationAuditFixture.rflWitness",
                rflWitnessAxiomFootprint=[],
                rflCheck={"lhs": "RelationAuditFixture.certDefId",
                          "rhs": "RelationAuditFixture.aliasDef"},
            )),
        make_certificate(
            "cert-impl", "implication", "RelationAuditFixture.certImpl",
            premises=[p_adj]),
        make_certificate(
            "cert-equiv", "equivalence", "RelationAuditFixture.certEquiv",
            premises=[p_pos]),
        make_certificate(
            "cert-comp", "conditionalComposition", "RelationAuditFixture.certComp",
            # The child certificate's canonical premise projection equals the
            # union of the two parent premise lists; the composition record
            # carries the same IDs.
            premises=[p_adj, p_pos],
            semantics=semantics_for(
                "Kasha ladder data -> Marcus barrier under hic.")),
        make_certificate(
            "cert-obs", "observationalEquivalence", "RelationAuditFixture.certObs",
            semantics=semantics_for(
                "Identity translation for the Stern-Volmer intensity channel.",
                channels=["intensity", "lifetime"])),
        make_certificate(
            "cert-dist", "distinguishability", "RelationAuditFixture.certDist",
            semantics=semantics_for(
                "Joint intensity-lifetime tracking translation.",
                form="identifiabilityDecoder",
                witness="RelationAuditFixture.distWitness",
                channels=["intensity", "lifetime"])),
        make_certificate(
            "cert-refu", "refutation", "RelationAuditFixture.certRefu",
            semantics=semantics_for(
                "Identity translation on the refuted implication.",
                counterexample="RelationAuditFixture.refuWitness",
                target="Unconditional Hammond gap -> Marcus barrier implication.")),
    ]

    records = [
        record("rec-def", "q-def", "marcus.barrier@7ad25a5", "certified",
               relation_kind="definitionalIdentity", certificate="cert-def"),
        record(
            "rec-impl", "q-impl", "bep.transfer@7ad25a5", "certified",
            relation_kind="implication", certificate="cert-impl",
            premises=[p_adj],
            badges={
                "explicit": {"earned": True, "premiseIds": ["p-adj"],
                             "note": "hAdj is a binder in lemmaImpl."},
            }),
        record(
            "rec-equiv", "q-equiv", "symmetry.factor@7ad25a5", "certified",
            relation_kind="equivalence", certificate="cert-equiv",
            premises=[p_pos],
            badges={
                "explicit": {"earned": True, "premiseIds": ["p-pos"],
                             "note": "hPos is a binder in lemmaEquiv."},
            }),
        record(
            "rec-comp", "q-comp", "kasha.rate@7ad25a5", "certified",
            relation_kind="conditionalComposition", certificate="cert-comp",
            premises=[
                {"id": p_adj["id"], "statement": p_adj["statement"]},
                {"id": p_pos["id"], "statement": p_pos["statement"]},
            ],
            composition={
                # The mock Lean certificate exposes the canonical projections;
                # JSON names the parent certificate IDs and the mediator only.
                # No combinator/application/childConclusion is reconstructed.
                "parents": ["cert-impl", "cert-equiv"],
                "mediators": ["marcus.barrier"],
                "translations": [{
                    "from": "kasha.rate",
                    "to": "marcus.barrier",
                    "description": "Transport the Kasha ladder statement into the Marcus context.",
                }],
                # Contract section 4: bridges may be empty when the parent
                # contexts already align; certificateBridgeIDs = [] pins it.
                "bridges": [],
                "discharges": [],
            }),
        record("rec-obs", "q-obs", "sternvolmer.intensity@7ad25a5", "certified",
               relation_kind="observationalEquivalence", certificate="cert-obs"),
        record("rec-dist", "q-dist", "sternvolmer.intensity@7ad25a5", "certified",
               relation_kind="distinguishability", certificate="cert-dist"),
        record("rec-refu", "q-refu", "hammond.gap@7ad25a5", "certified",
               relation_kind="refutation", certificate="cert-refu"),
        record(
            "rec-unres", "q-unres", "fluorphos.yield@7ad25a5", "unresolved",
            candidate="implication",
            rationale="Candidate coupling not yet delivered; registered without a certificate."),
        record(
            "rec-not", "q-not", "goldschmidt.tolerance@7ad25a5", "notEstablished",
            rationale="Scoped no-edge registration; no shared module or object.",
            dependencies=[{
                "kind": "sourceScan",
                "reference": "theories/RELATIONS.md",
                "recompute": "grep -n 'Goldschmidt' theories/RELATIONS.md",
            }]),
        record(
            "rec-out", "q-out", "raci.branching@7ad25a5", "outOfScope",
            scope="outside-genealogy",
            rationale="Both sides lie outside the agreed genealogy scope."),
    ]

    return {
        "schemaVersion": SCHEMA_VERSION,
        "mode": "pilot",
        "pairCount": 136,
        "snapshots": [snapshot],
        "scopes": scopes,
        "theoryInventory": [theory for theory, _, _, _ in THEORIES],
        "statements": statements,
        "queries": queries,
        "certificates": certificates,
        "records": records,
    }


def make_full() -> dict:
    statements, hashes = make_statements()
    scopes = [make_scopes()[0]]
    snapshot = make_snapshot(hashes)
    queries = []
    records = []
    for i, (source_theory, source_statement, _, _) in enumerate(THEORIES):
        for j in range(i + 1, len(THEORIES)):
            target_theory, target_statement, _, _ = THEORIES[j]
            query_id = f"q-full-{i:02d}-{j:02d}"
            queries.append(make_query(
                query_id, source_statement, target_statement,
                f"full registry {source_theory} / {target_theory}"))
            records.append(record(
                f"rec-full-{i:02d}-{j:02d}", query_id,
                f"{source_statement}@{SOURCE_SNAPSHOT[:7]}", "unresolved",
                candidate="implication",
                rationale="Registry-completeness record; no certificate claimed."))
    return {
        "schemaVersion": SCHEMA_VERSION,
        "mode": "full",
        "pairCount": 136,
        "snapshots": [snapshot],
        "scopes": scopes,
        "theoryInventory": [theory for theory, _, _, _ in THEORIES],
        "statements": statements,
        "queries": queries,
        "certificates": [],
        "records": records,
    }


def find_record(manifest: dict, record_id: str) -> dict:
    for item in manifest["records"]:
        if item["id"] == record_id:
            return item
    raise KeyError(record_id)


def find_certificate(manifest: dict, certificate_id: str) -> dict:
    for item in manifest["certificates"]:
        if item["id"] == certificate_id:
            return item
    raise KeyError(certificate_id)


def invalid_variants(pilot: dict, full: dict) -> dict[str, dict]:
    variants: dict[str, dict] = {}

    # A structural lie: the record and its certificate disagree about the kind.
    data = copy.deepcopy(pilot)
    find_record(data, "rec-equiv")["relationKind"] = "definitionalIdentity"
    variants["mislabelled_kind.json"] = data

    # A Lean lie: record and certificate both claim definitionalIdentity, but
    # the checked certificate value is an implication; only the generated
    # certificateKind rfl check can reject this.
    data = copy.deepcopy(pilot)
    rec = find_record(data, "rec-equiv")
    rec["relationKind"] = "definitionalIdentity"
    cert = find_certificate(data, "cert-equiv")
    cert["kind"] = "definitionalIdentity"
    cert["constructor"] = "RelationAuditFixture.CertificateKind.definitionalIdentity"
    cert["semantics"] = semantics_for(
        "claimed definitional translation",
        rflWitness="RelationAuditFixture.rflWitness",
        rflWitnessAxiomFootprint=[],
        rflCheck={"lhs": "RelationAuditFixture.certImpl",
                  "rhs": "RelationAuditFixture.aliasDef"})
    variants["mislabelled_kind_lean.json"] = data

    # A composition record that drops a parent premise without a discharge.
    data = copy.deepcopy(pilot)
    rec = find_record(data, "rec-comp")
    rec["premises"] = [item for item in rec["premises"] if item["id"] != "p-adj"]
    variants["missing_premise.json"] = data

    # A declared bridge without its statement text.  Empty bridges are legal;
    # a declared bridge must still be complete, and its witness is rejected
    # until typed bridge evidence exists.
    data = copy.deepcopy(pilot)
    rec = find_record(data, "rec-comp")
    rec["composition"]["bridges"] = [{
        "premiseId": "p-bridge",
        "witness": "RelationAuditFixture.bridgeWitness",
    }]
    rec["premises"].append(
        premise("p-bridge", "The Kasha ladder window implies the Marcus barrier inequality."))
    variants["incomplete_bridge.json"] = data

    # A declared bridge whose witness is an unrelated declaration.  The shape
    # is schema-valid (including expectedType); existence and an allowed axiom
    # footprint are still not bridge evidence (contract 6).
    data = copy.deepcopy(pilot)
    rec = find_record(data, "rec-comp")
    rec["composition"]["bridges"] = [{
        "premiseId": "p-bridge",
        "statement": "The Kasha ladder window implies the Marcus barrier inequality.",
        "expectedType": "True",
        "witness": "RelationAuditFixture.rflWitness",
    }]
    rec["premises"].append(
        premise("p-bridge", "The Kasha ladder window implies the Marcus barrier inequality."))
    variants["bridge_unrelated_witness.json"] = data

    # A declared discharge whose witness is an unrelated declaration.  The
    # premise closure would otherwise pass because the discharge covers the
    # omitted parent premise, so only the typed-evidence rejection catches it.
    data = copy.deepcopy(pilot)
    rec = find_record(data, "rec-comp")
    rec["premises"] = [item for item in rec["premises"] if item["id"] != "p-pos"]
    rec["composition"]["discharges"] = [{
        "premiseId": "p-pos",
        "retainedPremiseIds": ["p-adj"],
        "expectedType": "True",
        "witness": "RelationAuditFixture.rflWitness",
    }]
    variants["discharge_unrelated_witness.json"] = data

    # Badge claims backed only by an unrelated existing declaration.  The
    # objects are schema-valid (expectedType and premiseIds are present) so the
    # rejection must come from the typed-evidence rule, not from schema shape.
    data = copy.deepcopy(pilot)
    find_record(data, "rec-impl")["badges"]["nonvacuous"] = {
        "lean": "RelationAuditFixture.rflWitness",
        "expectedType": "True",
        "premiseIds": ["p-adj"],
    }
    variants["badge_nonvacuous_unrelated.json"] = data

    data = copy.deepcopy(pilot)
    find_record(data, "rec-impl")["badges"]["nonredundant"] = {
        "premiseIds": ["p-adj"],
        "byPremise": {
            "p-adj": {
                "lean": "RelationAuditFixture.rflWitness",
                "expectedType": "True",
            },
        },
    }
    variants["badge_nonredundant_unrelated.json"] = data

    data = copy.deepcopy(pilot)
    find_record(data, "rec-impl")["badges"]["weakest"] = {
        "premiseIds": ["p-adj"],
        "preorder": "premise-strength",
        "alternatives": ["p-adj"],
        "expectedType": "True",
        "minimality": "RelationAuditFixture.rflWitness",
    }
    variants["badge_weakest_unrelated.json"] = data

    # The two composition parents are swapped in the manifest.  The Lean
    # certificate's certificateParentIDs/certificateParentKinds still carry the
    # original left-to-right order, so the generated projection check rejects
    # the relabelling even though both parents resolve and are certified.
    data = copy.deepcopy(pilot)
    rec = find_record(data, "rec-comp")
    rec["composition"]["parents"] = ["cert-equiv", "cert-impl"]
    variants["composition_wrong_parent_order.json"] = data

    # The manifest changes a parent certificate's premise ID, but the Lean
    # parent value still carries the original premise.  Both the canonical
    # certificatePremiseIDs check and the composition parent-premise projection
    # reject it.
    data = copy.deepcopy(pilot)
    cert = find_certificate(data, "cert-equiv")
    cert["premises"] = [premise("p-pos-alias", "The reorganization energy is positive.")]
    rec = find_record(data, "rec-comp")
    for item in rec["premises"]:
        if item["id"] == "p-pos":
            item["id"] = "p-pos-alias"
    variants["composition_parent_premise_drift.json"] = data

    # The manifest points at a different mediating statement than the Lean
    # certificate's computed middle endpoint.
    data = copy.deepcopy(pilot)
    rec = find_record(data, "rec-comp")
    rec["composition"]["mediators"] = ["hammond.gap"]
    variants["composition_wrong_mediator.json"] = data

    # A snapshot whose commit does not exist in the repository.
    data = copy.deepcopy(pilot)
    data["snapshots"][0]["treeSha"] = "0" * 40
    variants["stale_snapshot.json"] = data

    # A snapshot whose pinned artifact hash no longer matches its commit.
    data = copy.deepcopy(pilot)
    data["snapshots"][0]["artifacts"]["PhotoLean/Marcus/Barrier.lean"] = "0" * 64
    variants["stale_artifact.json"] = data

    # Two records share (queryId, statementVersion, scope) with different statuses.
    data = copy.deepcopy(pilot)
    conflict = copy.deepcopy(find_record(data, "rec-equiv"))
    conflict["id"] = "rec-conflict"
    conflict["status"] = "unresolved"
    conflict["candidate"] = "implication"
    conflict.pop("relationKind", None)
    conflict.pop("certificate", None)
    conflict.pop("premises", None)
    conflict.pop("badges", None)
    conflict["rationale"] = "Conflicting status for the same query version and scope."
    conflict["provenance"]["rationale"] = conflict["rationale"]
    data["records"].append(conflict)
    variants["conflicting_statuses.json"] = data

    # Contract section 7: different certified kinds are not a conflict, so no
    # kind-exclusivity fixture exists here.  The coexistence case is a valid
    # manifest, exercised by the in-memory test in test_mutations.py.

    # Remove every record covering one pair (Einstein / RACI).
    data = copy.deepcopy(full)
    removed = {"rec-full-15-16", "q-full-15-16"}
    data["records"] = [r for r in data["records"] if r["id"] not in removed]
    data["queries"] = [q for q in data["queries"] if q["id"] not in removed]
    variants["missing_pair.json"] = data

    # Drop the record's provenance object.
    data = copy.deepcopy(pilot)
    find_record(data, "rec-def").pop("provenance")
    variants["missing_provenance.json"] = data

    # Certified record whose certificate id does not resolve.
    data = copy.deepcopy(pilot)
    find_record(data, "rec-def")["certificate"] = "cert-does-not-exist"
    variants["missing_certificate.json"] = data

    # 'adjudication' is a collection, not a primitive kind.
    data = copy.deepcopy(pilot)
    find_record(data, "rec-def")["relationKind"] = "adjudication"
    variants["adjudication_kind.json"] = data

    # notEstablished without machine-recomputable dependency evidence.
    data = copy.deepcopy(pilot)
    find_record(data, "rec-not").pop("dependencies")
    variants["missing_dependencies.json"] = data

    # A bare badge claim instead of structured evidence.
    data = copy.deepcopy(pilot)
    find_record(data, "rec-impl")["badges"]["nonvacuous"] = True
    variants["missing_badge_evidence.json"] = data

    # Duplicate record id.
    data = copy.deepcopy(pilot)
    duplicate = copy.deepcopy(find_record(data, "rec-def"))
    data["records"].append(duplicate)
    variants["duplicate_id.json"] = data

    # A record premise that no certificate or bridge carries.
    data = copy.deepcopy(pilot)
    rec = find_record(data, "rec-impl")
    rec["premises"].append(premise("p-extra", "An unregistered extra premise."))
    variants["unknown_premise.json"] = data

    # A scope that does not cover the record's endpoint theories.
    data = copy.deepcopy(pilot)
    find_record(data, "rec-def")["scope"] = "bep-kasha"
    variants["scope_jurisdiction.json"] = data

    return variants


def write_json(path: str, data: dict) -> None:
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2)
        handle.write("\n")


def main() -> int:
    if not os.path.isfile(os.path.join(REPO_ROOT, "proofs", "ENGINE.yml")):
        print(f"not inside the isolated checkout: {REPO_ROOT}", file=sys.stderr)
        return 2
    if not os.path.isfile(os.path.join(HERE, "schema.json")):
        print("fixtures/schema.json is missing", file=sys.stderr)
        return 2

    pilot = make_pilot()
    full = make_full()
    write_json(os.path.join(HERE, "manifest_pilot.json"), pilot)
    write_json(os.path.join(HERE, "manifest_full.json"), full)

    invalid_dir = os.path.join(HERE, "invalid")
    os.makedirs(invalid_dir, exist_ok=True)
    variants = invalid_variants(pilot, full)
    for name, data in variants.items():
        write_json(os.path.join(invalid_dir, name), data)
    # Remove one-defect fixtures that are no longer generated (for example the
    # retired `conflicting_kinds.json`: different certified kinds are not a
    # conflict under contract section 7).
    for existing in os.listdir(invalid_dir):
        if existing.endswith(".json") and existing not in variants:
            os.unlink(os.path.join(invalid_dir, existing))
            print(f"removed obsolete fixture {existing}")

    print(f"wrote pilot ({len(pilot['records'])} records), "
          f"full ({len(full['records'])} records), "
          f"and {len(variants)} invalid fixtures")
    return 0


if __name__ == "__main__":
    sys.exit(main())

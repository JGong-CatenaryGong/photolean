"""Adapter between the checked-in JSON schema and the audit's semantic model.

The contract freezes the artifact layout (``relation_audit/schema.json`` and
``relation_audit/pilot.json``) but not the exact property spellings that the
schema author chooses.  This module discovers the object definitions in the
schema and resolves the canonical audit fields through a small alias table.
It never edits or rewrites the schema.

If a canonical field cannot be located in the schema or in the manifest, the
caller reports ``interface.missingField`` and the audit fails closed; the exact
expected interface is documented in ``tools/relation_audit/INTERFACE.md``.
"""

from __future__ import annotations

from typing import Any

from . import json_schema


_MISSING = object()


# Canonical field -> accepted spellings, in preference order.
ALIASES: dict[str, dict[str, tuple[str, ...]]] = {
    "manifest": {
        "schemaVersion": ("schemaVersion", "version", "contractVersion"),
        "mode": ("mode", "auditMode"),
        "pairCount": ("pairCount", "pairCountExpected", "expectedPairCount"),
        "description": ("description", "summary"),
        "theoryInventory": ("theoryInventory", "theories", "theoryIds",
                            "theory_ids", "inventory"),
        "snapshots": ("snapshots", "snapshotRegistry", "snapshot"),
        "scopes": ("scopes", "scopeRegistry"),
        "statements": ("statements", "statementRegistry", "statementRefs"),
        "queries": ("queries", "queryRegistry", "queryRefs"),
        "certificates": ("certificates", "certificateRegistry", "certificateRows"),
        "records": ("records", "auditRecords", "audits", "registry", "entries"),
    },
    "snapshot": {
        "id": ("id", "snapshotId", "snapshotID"),
        "treeSha": ("treeSha", "commit", "headSha", "sourceSnapshot", "treeSHA"),
        "toolchain": ("toolchain", "toolchainHash", "leanToolchain"),
        "schemaSha256": ("schemaSha256", "schemaHash", "schemaSHA256"),
        "mathlibRev": ("mathlibRev", "mathlibRevision", "mathlibSha"),
        "dirty": ("dirty", "workingTreeDirty"),
        "artifacts": ("artifacts", "hashes", "artifactHashes"),
    },
    "scope": {
        "id": ("id", "scopeId", "scopeID"),
        "kind": ("kind", "type", "scopeKind"),
        "description": ("description", "summary"),
        "theories": ("theories", "theoryIds", "jurisdiction"),
        "provenance": ("provenance", "sources"),
    },
    "statement": {
        "id": ("id", "statementId", "statementID"),
        "theory": ("theory", "theoryId", "theoryID"),
        "artifact": ("artifact", "artifactPath", "file"),
        "sha256": ("sha256", "artifactHash", "hash", "versionHash"),
        "version": ("version", "statementVersion", "semver"),
        "context": ("context", "statementContext"),
        "declaration": ("declaration", "lean", "leanDeclaration"),
        "provenance": ("provenance", "sources"),
    },
    "query": {
        "id": ("id", "queryId", "queryID"),
        "source": ("source", "from", "sourceStatement"),
        "target": ("target", "to", "targetStatement"),
        "context": ("context", "sharedContext"),
        "provenance": ("provenance", "sources"),
    },
    "certificate": {
        "id": ("id", "certificateId", "certificateID"),
        "kind": ("kind", "relationKind", "certificateKind"),
        "module": ("module", "leanModule", "import"),
        "lean": ("lean", "declaration", "certificateName", "name"),
        "kindFunction": ("kindFunction", "certificateKindFunction", "kindFn"),
        "constructor": ("constructor", "kindConstructor", "kindTerm"),
        "premises": ("premises", "assumptions"),
        "semantics": ("semantics", "evidence"),
        "axiomFootprint": ("axiomFootprint", "axioms", "printedAxioms"),
        "sourcePath": ("sourcePath", "sourceFile", "artifact"),
        "sourceSha256": ("sourceSha256", "sourceHash", "sha256"),
    },
    "premise": {
        "id": ("id", "premiseId", "premiseID"),
        "statement": ("statement", "proposition", "text"),
        "explicit": ("explicit", "inSignature", "isExplicit"),
        "role": ("role", "premiseRole"),
        "signatureName": ("signatureName", "binder", "binderName"),
        "signatureDeclaration": ("signatureDeclaration", "signature", "declaration"),
    },
    "record": {
        "id": ("id", "recordId", "recordID", "auditId"),
        "queryId": ("queryId", "queryID", "query"),
        "statementVersion": ("statementVersion", "version", "statementHash"),
        "scope": ("scope", "scopeId", "scopeID"),
        "status": ("status", "auditStatus"),
        "relationKind": ("relationKind", "kind", "relation"),
        "certificate": ("certificate", "certificateId", "certificateRef"),
        "snapshot": ("snapshot", "snapshotId", "snapshotRef"),
        "rationale": ("rationale", "reason", "justification"),
        "candidate": ("candidate", "candidateKind", "proposedKind"),
        "premises": ("premises", "assumptions"),
        "badges": ("badges", "premiseBadges"),
        "composition": ("composition", "compositionEvidence"),
        "dependencies": ("dependencies", "dependencyEvidence"),
        "provenance": ("provenance", "sources"),
    },
    "composition": {
        "parents": ("parents", "parentCertificates"),
        "mediators": ("mediators", "mediatingEndpoints"),
        "translations": ("translations", "translationEdges"),
        "bridges": ("bridges", "bridgePremises"),
        "discharges": ("discharges", "dischargeCertificates"),
    },
    "bridge": {
        "premiseId": ("premiseId", "premiseID", "premise"),
        "statement": ("statement", "proposition"),
        "witness": ("witness", "lean", "declaration"),
    },
    "discharge": {
        "premiseId": ("premiseId", "premiseID", "premise"),
        "witness": ("witness", "lean", "declaration"),
    },
    "badge": {
        "kind": ("kind", "type"),
        "earned": ("earned", "claimed", "present"),
        "lean": ("lean", "witness", "declaration"),
        "premiseIds": ("premiseIds", "premise_ids", "premises"),
        "byPremise": ("byPremise", "perPremise", "witnesses"),
        "preorder": ("preorder", "order"),
        "alternatives": ("alternatives", "alternativePremises"),
        "minimality": ("minimality", "minimalityCertificate", "lean"),
    },
    "dependency": {
        "kind": ("kind", "type"),
        "reference": ("reference", "artifact", "target"),
        "recompute": ("recompute", "command", "recomputeCommand"),
        "sha256": ("sha256", "hash"),
    },
    "semantics": {
        "context": ("context", "sharedContext"),
        "translations": ("translations", "translationEdges"),
        "premisePredicate": ("premisePredicate", "premisesPredicate"),
        "translation": ("translation", "translationDescription"),
        "rflWitness": ("rflWitness", "rflCertificate", "definitionalWitness"),
        "rflWitnessAxiomFootprint": ("rflWitnessAxiomFootprint", "rflWitnessAxioms",
                                     "definitionalWitnessAxiomFootprint"),
        "rflCheck": ("rflCheck", "rflEquality"),
        "channels": ("channels", "observationChannels"),
        "channelSpecs": ("channelSpecs", "observations"),
        "form": ("form", "witnessForm"),
        "witness": ("witness", "distinguishingWitness", "decoderCertificate"),
        "counterexample": ("counterexample", "refutationWitness"),
        "target": ("target", "refutedImplication"),
    },
    "provenance": {
        "kind": ("kind", "type"),
        "references": ("references", "sources", "refs"),
        "rationale": ("rationale", "note", "reason"),
    },
    "reference": {
        "artifact": ("artifact", "path", "file", "uri"),
        "locator": ("locator", "anchor", "line"),
    },
}


# Distinguishing fields used to find the schema definition for each object kind.
DEF_SIGNATURES: dict[str, tuple[str, ...]] = {
    "snapshot": ("treeSha", "toolchain", "schemaSha256", "artifacts"),
    "scope": ("description", "provenance", "kind"),
    "statement": ("theory", "artifact", "sha256", "provenance"),
    "query": ("source", "target", "context", "provenance"),
    "certificate": ("lean", "kindFunction", "constructor", "module", "kind"),
    "record": ("queryId", "statementVersion", "status", "snapshot", "certificate"),
    "composition": ("parents", "mediators", "translations", "bridges"),
    "dependency": ("recompute", "reference", "kind"),
    "provenance": ("kind", "references"),
    "semantics": ("context", "translations", "premisePredicate", "channels",
                  "rflWitness", "counterexample", "form", "translation"),
}

DEF_NAME_HINTS: dict[str, tuple[str, ...]] = {
    "manifest": ("manifest", "registry", "pilot", "audit"),
    "snapshot": ("snapshot",),
    "scope": ("scope",),
    "statement": ("statement", "endpoint"),
    "query": ("query",),
    "certificate": ("certificate",),
    "record": ("record", "audit", "entry"),
    "composition": ("composition",),
    "dependency": ("dependency",),
    "provenance": ("provenance", "source"),
    "semantics": ("semantics", "evidence"),
}


class InterfaceError(Exception):
    def __init__(self, kind: str, field: str):
        super().__init__(f"cannot locate canonical field {field!r} for object {kind!r}")
        self.kind = kind
        self.field = field


class SchemaInterface:
    """Resolves canonical audit fields using the checked-in schema."""

    def __init__(self, schema: json_schema.Schema):
        self.schema = schema
        self._defs = schema.definitions()
        self._def_cache: dict[str, Any] = {}
        self._field_cache: dict[str, dict[str, str]] = {}
        self._discovered: dict[str, str] = {}

    # ------------------------------------------------------------- discovery
    def _root(self) -> Any:
        try:
            return self.schema.deref(self.schema.document)
        except json_schema.SchemaError:
            return self.schema.document

    def definition(self, kind: str) -> Any:
        if kind in self._def_cache:
            return self._def_cache[kind]
        if kind == "manifest":
            root = self._root()
            if isinstance(root, dict) and isinstance(root.get("properties"), dict):
                self._def_cache[kind] = root
                self._discovered[kind] = "<root>"
                return root
        if kind not in DEF_SIGNATURES and kind not in DEF_NAME_HINTS:
            self._def_cache[kind] = {}
            self._discovered[kind] = "<absent>"
            return {}
        best_name, best_node, best_score = None, None, -1
        for name in sorted(self._defs):
            try:
                node = self.schema.deref(self._defs[name])
            except json_schema.SchemaError:
                continue
            if not isinstance(node, dict):
                continue
            props = node.get("properties", {})
            if not isinstance(props, dict):
                continue
            score = 0
            for canonical in DEF_SIGNATURES.get(kind, ()):  # type: ignore[arg-type]
                if any(alias in props for alias in ALIASES[kind][canonical]):
                    score += 1
            lowered = name.lower()
            if any(hint in lowered for hint in DEF_NAME_HINTS.get(kind, ())):
                score += 3
            if score > best_score:
                best_name, best_node, best_score = name, node, score
        if best_node is None or best_score <= 0:
            best_node = {}
            best_name = "<absent>"
        self._def_cache[kind] = best_node
        self._discovered[kind] = best_name
        return best_node

    def discovered(self) -> dict[str, str]:
        for kind in ALIASES:
            self.definition(kind)
        return dict(self._discovered)

    # ---------------------------------------------------------------- fields
    def fields(self, kind: str) -> dict[str, str]:
        if kind in self._field_cache:
            return self._field_cache[kind]
        node = self.definition(kind)
        props = node.get("properties", {}) if isinstance(node, dict) else {}
        if not isinstance(props, dict):
            props = {}
        mapping: dict[str, str] = {}
        for canonical, aliases in ALIASES[kind].items():
            chosen = canonical
            for alias in aliases:
                if alias in props:
                    chosen = alias
                    break
            mapping[canonical] = chosen
        self._field_cache[kind] = mapping
        return mapping

    def get(self, obj: Any, kind: str, canonical: str, default: Any = _MISSING) -> Any:
        """Read a canonical field from an object, tolerating schema renames."""
        if not isinstance(obj, dict):
            return default
        actual = self.fields(kind).get(canonical, canonical)
        if actual in obj:
            return obj[actual]
        for alias in ALIASES[kind].get(canonical, ()):
            if alias in obj:
                return obj[alias]
        if default is _MISSING:
            raise InterfaceError(kind, canonical)
        return default

    def has(self, obj: Any, kind: str, canonical: str) -> bool:
        try:
            self.get(obj, kind, canonical)
            return True
        except InterfaceError:
            return False

    def enum(self, kind: str, canonical: str) -> list[Any] | None:
        """Return an enum declared by the schema for a canonical field, if any."""
        node = self.definition(kind)
        props = node.get("properties", {}) if isinstance(node, dict) else {}
        actual = self.fields(kind).get(canonical, canonical)
        prop = props.get(actual) if isinstance(props, dict) else None
        if isinstance(prop, dict) and isinstance(prop.get("enum"), list):
            return list(prop["enum"])
        return None

    def expected_interface(self) -> dict[str, dict[str, str]]:
        """Human-readable summary of the fields the validator will read."""
        summary: dict[str, dict[str, str]] = {}
        for kind in ALIASES:
            node = self.definition(kind)
            summary[kind] = {
                "definition": self._discovered.get(kind, "<absent>"),
                "fields": {canonical: self.fields(kind)[canonical]
                           for canonical in ALIASES[kind]},
            }
            if isinstance(node, dict) and node.get("required"):
                summary[kind]["required"] = list(node["required"])  # type: ignore[assignment]
        return summary

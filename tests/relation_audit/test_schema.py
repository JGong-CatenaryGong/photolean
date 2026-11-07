"""Tests for the fail-closed JSON-schema subset and the schema adapter."""

from __future__ import annotations

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), "tools"))

from harness import FIXTURES, PILOT, REPO_ROOT  # noqa: E402
from relation_audit import json_schema  # noqa: E402
from relation_audit.interface import SchemaInterface  # noqa: E402


SCHEMA_PATH = os.path.join(FIXTURES, "schema.json")


class JsonSchemaTests(unittest.TestCase):
    def test_fixture_schema_accepts_valid_manifest(self):
        schema = json_schema.Schema.from_path(SCHEMA_PATH)
        with open(PILOT, encoding="utf-8") as handle:
            import json
            manifest = json.load(handle)
        self.assertEqual(schema.validate(manifest), [])

    def test_type_and_required(self):
        schema = json_schema.Schema({
            "type": "object",
            "required": ["id", "status"],
            "properties": {"id": {"type": "string"},
                           "status": {"type": "string", "enum": ["a", "b"]}},
            "additionalProperties": False,
        })
        self.assertEqual(schema.validate({"id": "x", "status": "a"}), [])
        self.assertTrue(schema.validate({"id": 1, "status": "c"}))
        self.assertTrue(schema.validate({"id": "x"}))
        self.assertTrue(schema.validate({"id": "x", "status": "a", "extra": 1}))

    def test_local_ref_and_items(self):
        schema = json_schema.Schema({
            "type": "array",
            "minItems": 2,
            "uniqueItems": True,
            "items": {"$ref": "#/$defs/Row"},
            "$defs": {"Row": {
                "type": "object",
                "required": ["id"],
                "properties": {"id": {"type": "string", "minLength": 1}},
                "additionalProperties": False,
            }},
        })
        self.assertEqual(schema.validate([{"id": "a"}, {"id": "b"}]), [])
        self.assertTrue(schema.validate([{"id": "a"}]))
        self.assertTrue(schema.validate([{"id": "a"}, {"id": "a"}]))
        self.assertTrue(schema.validate([{"id": "a"}, {"id": 2}]))

    def test_unsupported_keyword_is_an_error(self):
        with self.assertRaises(json_schema.SchemaError):
            json_schema.Schema({"type": "object", "unevaluatedProperties": False})
        with self.assertRaises(json_schema.SchemaError):
            json_schema.Schema({"type": "object", "properties": {
                "x": {"type": "string", "unknownConstraint": 1}}})

    def test_external_ref_is_rejected(self):
        with self.assertRaises(json_schema.SchemaError):
            json_schema.Schema({"$ref": "https://example.com/schema.json"})

    def test_boolean_schema(self):
        self.assertEqual(json_schema.Schema(True).validate(1), [])
        self.assertTrue(json_schema.Schema(False).validate(1))


PRODUCTION_SCHEMA = os.path.join(REPO_ROOT, "relation_audit", "schema.json")


class ProductionSchemaAdapterTests(unittest.TestCase):
    """The adapter must read the lead-owned schema without editing it."""

    @unittest.skipUnless(os.path.isfile(PRODUCTION_SCHEMA),
                         "production relation_audit/schema.json not present")
    def test_production_schema_definitions_are_discovered(self):
        schema = json_schema.Schema.from_path(PRODUCTION_SCHEMA)
        interface = SchemaInterface(schema)
        discovered = interface.discovered()
        for kind, definition in (("record", "record"), ("certificate", "certificate"),
                                 ("snapshot", "snapshot"), ("scope", "scope"),
                                 ("statement", "statement"), ("query", "query")):
            self.assertEqual(discovered[kind], definition)
        self.assertEqual(interface.fields("record")["queryId"], "queryId")
        self.assertEqual(interface.fields("scope")["theories"], "theories")
        self.assertEqual(interface.fields("certificate")["axiomFootprint"],
                         "axiomFootprint")
        self.assertEqual(interface.fields("semantics")["premisePredicate"],
                         "premisePredicate")

class InterfaceTests(unittest.TestCase):
    def setUp(self):
        self.schema = json_schema.Schema.from_path(SCHEMA_PATH)
        self.interface = SchemaInterface(self.schema)

    def test_definitions_are_discovered(self):
        discovered = self.interface.discovered()
        self.assertEqual(discovered["manifest"], "<root>")
        # Definition names are lower-case in the v1.1.0 schema copy; accept
        # either casing so the adapter test is not coupled to the schema author's
        # naming convention.
        self.assertEqual(discovered["record"].lower(), "record")
        self.assertEqual(discovered["certificate"].lower(), "certificate")
        self.assertEqual(discovered["snapshot"].lower(), "snapshot")

    def test_canonical_fields_resolve_to_schema_properties(self):
        fields = self.interface.fields("record")
        for canonical in ("id", "queryId", "statementVersion", "status",
                          "relationKind", "certificate", "snapshot", "premises",
                          "badges", "composition", "provenance"):
            self.assertEqual(fields[canonical], canonical)
        self.assertEqual(self.interface.fields("certificate")["kindFunction"],
                         "kindFunction")

    def test_get_tolerates_spelling_alias_when_reading(self):
        # Even if a schema renames the property, reading through an alias works.
        self.assertEqual(self.interface.get({"queryID": "q"}, "record", "queryId"), "q")
        self.assertEqual(self.interface.get({"auditStatus": "certified"},
                                            "record", "status"), "certified")

    def test_expected_interface_mentions_every_core_object(self):
        summary = self.interface.expected_interface()
        for kind in ("manifest", "snapshot", "scope", "statement", "query",
                     "certificate", "record"):
            self.assertIn(kind, summary)
            self.assertNotEqual(summary[kind]["definition"], "<absent>")

    def test_fixture_is_the_isolated_checkout(self):
        self.assertTrue(os.path.isfile(os.path.join(REPO_ROOT, "proofs", "ENGINE.yml")))


if __name__ == "__main__":
    unittest.main()

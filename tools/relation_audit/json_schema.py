"""A small, fail-closed JSON Schema validator (standard library only).

The relation audit must adapt to the checked-in manifest schema without editing
it.  Rather than importing a third-party validator, this module implements the
subset of JSON Schema 2020-12 that the audit contract needs.  The important
property is *fail-closed*: a schema keyword this module does not understand is
reported as an error, never silently ignored.  Otherwise a later schema
revision could weaken the gate without anybody noticing.

Supported assertion keywords:
    $ref (local pointers only), type, enum, const, required, properties,
    additionalProperties, patternProperties, propertyNames, items,
    prefixItems, minItems, maxItems, uniqueItems, minLength, maxLength,
    pattern, minimum, maximum, exclusiveMinimum, exclusiveMaximum,
    multipleOf, allOf, anyOf, oneOf, not, if/then/else.

Annotation keywords are accepted and ignored (they do not constrain data):
    $schema, $id, $comment, $defs, definitions, title, description, default,
    examples, deprecated, readOnly, writeOnly, format, contentMediaType,
    contentEncoding.

Everything else is an error.  External ``$ref`` values are errors as well:
the validator is not allowed to fetch anything.
"""

from __future__ import annotations

import json
import re
from typing import Any


ANNOTATION_KEYWORDS = {
    "$schema", "$id", "$comment", "$defs", "definitions", "title",
    "description", "default", "examples", "deprecated", "readOnly",
    "writeOnly", "format", "contentMediaType", "contentEncoding",
}

SUPPORTED_KEYWORDS = ANNOTATION_KEYWORDS | {
    "$ref", "type", "enum", "const", "required", "properties",
    "additionalProperties", "patternProperties", "propertyNames", "items",
    "prefixItems", "minItems", "maxItems", "uniqueItems", "minProperties",
    "maxProperties", "minLength", "maxLength", "pattern", "minimum", "maximum",
    "exclusiveMinimum",
    "exclusiveMaximum", "multipleOf", "allOf", "anyOf", "oneOf", "not",
    "if", "then", "else",
}

_JSON_TYPES = {"null", "boolean", "object", "array", "string", "number", "integer"}


def json_equal(left: Any, right: Any) -> bool:
    """Strict JSON equality (``True`` does not equal ``1``)."""
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return (left.keys() == right.keys()
                and all(json_equal(left[k], right[k]) for k in left))
    if isinstance(left, list):
        return (len(left) == len(right)
                and all(json_equal(a, b) for a, b in zip(left, right)))
    return left == right


def _is_type(value: Any, name: str) -> bool:
    if name == "null":
        return value is None
    if name == "boolean":
        return isinstance(value, bool)
    if name == "object":
        return isinstance(value, dict)
    if name == "array":
        return isinstance(value, list)
    if name == "string":
        return isinstance(value, str)
    if name == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if name == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    return False


def _pointer_unescape(token: str) -> str:
    return token.replace("~1", "/").replace("~0", "~")


class SchemaError(Exception):
    """Raised for a malformed or unsupported schema document."""

    def __init__(self, pointer: str, message: str):
        super().__init__(f"{pointer or '/'}: {message}")
        self.pointer = pointer
        self.message = message


class ValidationError:
    def __init__(self, path: str, message: str):
        self.path = path
        self.message = message

    def __str__(self) -> str:
        return f"{self.path or '$'}: {self.message}"


class Schema:
    """Loads a schema document and validates instances against it."""

    def __init__(self, document: Any):
        if not isinstance(document, (dict, bool)):
            raise SchemaError("", "schema document must be an object or a boolean")
        self.document = document
        self._check_keywords(document, "")

    # ------------------------------------------------------------------ loading
    @classmethod
    def from_path(cls, path: str) -> "Schema":
        with open(path, encoding="utf-8") as handle:
            document = json.load(handle)
        return cls(document)

    # --------------------------------------------------------------- discovery
    def definitions(self) -> dict[str, Any]:
        """Return the local definition table (``$defs`` or ``definitions``)."""
        if not isinstance(self.document, dict):
            return {}
        table = self.document.get("$defs", self.document.get("definitions", {}))
        return table if isinstance(table, dict) else {}

    def resolve(self, ref: Any) -> Any:
        """Resolve a local ``$ref``; raise for external or dangling references."""
        if not isinstance(ref, str):
            raise SchemaError("", f"$ref must be a string, got {type(ref).__name__}")
        if not ref.startswith("#"):
            raise SchemaError("", f"external $ref {ref!r} is not allowed")
        node: Any = self.document
        if ref == "#":
            return node
        if not ref.startswith("#/"):
            raise SchemaError("", f"unsupported $ref {ref!r}")
        for raw in ref[2:].split("/"):
            token = _pointer_unescape(raw)
            if isinstance(node, dict) and token in node:
                node = node[token]
            elif isinstance(node, list) and token.isdigit() and int(token) < len(node):
                node = node[int(token)]
            else:
                raise SchemaError("", f"dangling $ref {ref!r}")
        return node

    def deref(self, node: Any) -> Any:
        """Follow ``$ref`` chains (cycle guarded)."""
        seen: set[str] = set()
        while isinstance(node, dict) and "$ref" in node:
            ref = node["$ref"]
            if ref in seen:
                raise SchemaError("", f"cyclic $ref {ref!r}")
            seen.add(ref)
            node = self.resolve(ref)
        return node

    # ------------------------------------------------------------------- checks
    def _check_keywords(self, node: Any, pointer: str) -> None:
        """Reject any keyword outside the supported subset (fail closed)."""
        if isinstance(node, bool):
            return
        if not isinstance(node, dict):
            raise SchemaError(pointer, "schema nodes must be objects or booleans")
        for key, value in node.items():
            if key not in SUPPORTED_KEYWORDS:
                raise SchemaError(pointer, f"unsupported schema keyword {key!r}")
            child = f"{pointer}/{key}"
            if key in ("properties", "patternProperties", "$defs", "definitions"):
                if not isinstance(value, dict):
                    raise SchemaError(child, "must be an object")
                for name, subschema in value.items():
                    self._check_keywords(subschema, f"{child}/{name}")
            elif key in ("allOf", "anyOf", "oneOf", "prefixItems"):
                if not isinstance(value, list):
                    raise SchemaError(child, "must be an array")
                for index, subschema in enumerate(value):
                    self._check_keywords(subschema, f"{child}/{index}")
            elif key in ("items", "additionalProperties", "propertyNames",
                         "not", "if", "then", "else"):
                if key == "items" and isinstance(value, list):
                    raise SchemaError(child, "array-form 'items' is not supported; use prefixItems")
                self._check_keywords(value, child)
        if "$ref" in node:
            # Resolve now so dangling/external references fail at load time.
            self.resolve(node["$ref"])

    # -------------------------------------------------------------- validation
    def validate(self, instance: Any) -> list[ValidationError]:
        errors: list[ValidationError] = []
        self._validate(instance, self.document, "", errors)
        return errors

    def _validate(self, instance: Any, node: Any, path: str, errors: list[ValidationError]) -> None:
        node = self.deref(node)
        if node is True:
            return
        if node is False:
            errors.append(ValidationError(path, "no value is allowed here"))
            return
        if not isinstance(node, dict):
            errors.append(ValidationError(path, "malformed schema node"))
            return

        if "type" in node:
            self._check_type(instance, node["type"], path, errors)
        if "enum" in node:
            if not any(json_equal(instance, candidate) for candidate in node["enum"]):
                errors.append(ValidationError(path, f"value is not one of {node['enum']!r}"))
        if "const" in node:
            if not json_equal(instance, node["const"]):
                errors.append(ValidationError(path, f"value must equal {node['const']!r}"))

        self._validate_combinators(instance, node, path, errors)

        if isinstance(instance, dict):
            self._validate_object(instance, node, path, errors)
        elif isinstance(instance, list):
            self._validate_array(instance, node, path, errors)
        elif isinstance(instance, str):
            self._validate_string(instance, node, path, errors)
        elif isinstance(instance, (int, float)) and not isinstance(instance, bool):
            self._validate_number(instance, node, path, errors)

    def _check_type(self, instance: Any, expected: Any, path: str,
                    errors: list[ValidationError]) -> None:
        names = expected if isinstance(expected, list) else [expected]
        if not names or any(name not in _JSON_TYPES for name in names):
            errors.append(ValidationError(path, f"schema has an invalid type list {expected!r}"))
            return
        if not any(_is_type(instance, name) for name in names):
            errors.append(ValidationError(path, f"expected type {expected!r}"))

    def _validate_combinators(self, instance: Any, node: dict, path: str,
                              errors: list[ValidationError]) -> None:
        if "allOf" in node:
            for subschema in node["allOf"]:
                self._validate(instance, subschema, path, errors)
        if "anyOf" in node:
            local: list[ValidationError] = []
            for subschema in node["anyOf"]:
                branch: list[ValidationError] = []
                self._validate(instance, subschema, path, branch)
                local.extend(branch)
                if not branch:
                    break
            else:
                errors.append(ValidationError(path, "value matches none of the anyOf branches"))
        if "oneOf" in node:
            matches = 0
            for subschema in node["oneOf"]:
                branch: list[ValidationError] = []
                self._validate(instance, subschema, path, branch)
                if not branch:
                    matches += 1
            if matches != 1:
                errors.append(ValidationError(
                    path, f"value must match exactly one oneOf branch (matched {matches})"))
        if "not" in node:
            branch = []
            self._validate(instance, node["not"], path, branch)
            if not branch:
                errors.append(ValidationError(path, "value matches a 'not' schema"))
        if "if" in node:
            condition: list[ValidationError] = []
            self._validate(instance, node["if"], path, condition)
            branch_name = "then" if not condition else "else"
            if branch_name in node:
                self._validate(instance, node[branch_name], path, errors)

    def _validate_object(self, instance: dict, node: dict, path: str,
                         errors: list[ValidationError]) -> None:
        properties = node.get("properties", {})
        patterns = node.get("patternProperties", {})
        required = node.get("required", [])
        if not isinstance(required, list):
            errors.append(ValidationError(path, "schema 'required' must be an array"))
            required = []
        for name in required:
            if name not in instance:
                errors.append(ValidationError(path, f"missing required property {name!r}"))

        for name, value in instance.items():
            matched = False
            if name in properties:
                matched = True
                self._validate(value, properties[name], self._join(path, name), errors)
            for pattern, subschema in patterns.items():
                try:
                    hit = re.search(pattern, name) is not None
                except re.error:
                    errors.append(ValidationError(path, f"invalid patternProperties regex {pattern!r}"))
                    continue
                if hit:
                    matched = True
                    self._validate(value, subschema, self._join(path, name), errors)
            if not matched and "additionalProperties" in node:
                extra = node["additionalProperties"]
                if extra is False:
                    errors.append(ValidationError(path, f"additional property {name!r} is not allowed"))
                elif extra is not True:
                    self._validate(value, extra, self._join(path, name), errors)
        if "minProperties" in node and len(instance) < node["minProperties"]:
            errors.append(ValidationError(path, f"expected at least {node['minProperties']} properties"))
        if "maxProperties" in node and len(instance) > node["maxProperties"]:
            errors.append(ValidationError(path, f"expected at most {node['maxProperties']} properties"))
        if "propertyNames" in node:
            for name in instance:
                self._validate(name, node["propertyNames"], self._join(path, name), errors)

    def _validate_array(self, instance: list, node: dict, path: str,
                        errors: list[ValidationError]) -> None:
        prefix = node.get("prefixItems", [])
        for index, subschema in enumerate(prefix):
            if index < len(instance):
                self._validate(instance[index], subschema, f"{path}[{index}]", errors)
        if "items" in node:
            start = len(prefix)
            for index in range(start, len(instance)):
                self._validate(instance[index], node["items"], f"{path}[{index}]", errors)
        if "minItems" in node and len(instance) < node["minItems"]:
            errors.append(ValidationError(path, f"expected at least {node['minItems']} items"))
        if "maxItems" in node and len(instance) > node["maxItems"]:
            errors.append(ValidationError(path, f"expected at most {node['maxItems']} items"))
        if node.get("uniqueItems") is True:
            for i in range(len(instance)):
                for j in range(i + 1, len(instance)):
                    if json_equal(instance[i], instance[j]):
                        errors.append(ValidationError(path, f"items {i} and {j} are not unique"))

    def _validate_string(self, instance: str, node: dict, path: str,
                         errors: list[ValidationError]) -> None:
        if "minLength" in node and len(instance) < node["minLength"]:
            errors.append(ValidationError(path, f"string shorter than {node['minLength']}"))
        if "maxLength" in node and len(instance) > node["maxLength"]:
            errors.append(ValidationError(path, f"string longer than {node['maxLength']}"))
        if "pattern" in node:
            try:
                if re.search(node["pattern"], instance) is None:
                    errors.append(ValidationError(path, f"string does not match {node['pattern']!r}"))
            except re.error:
                errors.append(ValidationError(path, f"invalid pattern {node['pattern']!r}"))

    def _validate_number(self, instance: float, node: dict, path: str,
                         errors: list[ValidationError]) -> None:
        if "minimum" in node and instance < node["minimum"]:
            errors.append(ValidationError(path, f"number less than minimum {node['minimum']}"))
        if "maximum" in node and instance > node["maximum"]:
            errors.append(ValidationError(path, f"number greater than maximum {node['maximum']}"))
        if "exclusiveMinimum" in node and instance <= node["exclusiveMinimum"]:
            errors.append(ValidationError(path, f"number not greater than {node['exclusiveMinimum']}"))
        if "exclusiveMaximum" in node and instance >= node["exclusiveMaximum"]:
            errors.append(ValidationError(path, f"number not less than {node['exclusiveMaximum']}"))
        if "multipleOf" in node:
            divisor = node["multipleOf"]
            if not isinstance(divisor, (int, float)) or divisor == 0:
                errors.append(ValidationError(path, "schema has an invalid multipleOf"))
            elif abs(instance / divisor - round(instance / divisor)) > 1e-9:
                errors.append(ValidationError(path, f"number is not a multiple of {divisor}"))

    @staticmethod
    def _join(path: str, name: str) -> str:
        return f"{path}.{name}" if path else name

# Scoped angle-typed torsion variant

`AngleTorsion.lean` is an **additive, out-of-manifest** companion to the retained
Real-coordinate RACI torsion model (`PhotoLean/RACI/Torsion.lean`). It answers the
referee's torsion-typing concern by exhibiting a genuinely **periodic** angle type
(the unit circle in `ℂ`) rather than a Real local coordinate. The blocking theorem
uses only a continuous real-valued chord distance to the conical intersection and
the intermediate value theorem on the real path parameter — it never assumes a
global linear order or absolute value on the circle.

## Isolation guarantees (do not break these)

- Intended release path: `extensions/RACI/AngleTorsion.lean` — **outside** the frozen
  `PhotoLean/**` manifest. The 102-file / 1,154-row denominators and every census
  hash stay byte-identical.
- **Outside** the pinned nine-probe validation set. The 9 probes / 58 declarations /
  31,347 checks / 67 certified counts stay unchanged.
- **Zero active pair/query coverage**: this is theory-level evidence only. No census
  record, probe, or rate-layer certificate references it (grep-verified).
- No `sorry`, no custom `axiom`. Axiom footprint of every delivered theorem is
  exactly `[propext, Classical.choice, Quot.sound]`.

## mathlib version caveat (important)

The pinned reviewer-facing release uses **Lean v4.17.0 / mathlib rev
`5269898d6a51`**. The module was **machine-checked locally under Lean v4.33.1 /
mathlib rev `0df444a360ea`** (the only fully built mathlib environment available on
the authoring machine), where `lake env lean AngleTorsion.lean` exits 0 with no
errors, no warnings and no `sorry`.

A full **pinned-toolchain (v4.17.0) rebuild was not run locally**: the authoring
machine has no GitHub network access, and the local v4.17.0 checkout is missing
eight dependency packages with its mathlib at a non-manifest revision, so its
olean cache cannot be materialised offline.

To compensate, **every mathlib API used by the module is source-verified against
the pinned v4.17.0 mathlib** (`raci_lean/repo`, manifest rev `5269898d6a51`):

| API | v4.17.0 source location |
| --- | --- |
| `continuous_subtype_val` | `Topology/Constructions.lean:380` |
| `Continuous.dist` | `Topology/MetricSpace/Pseudo/Constructions.lean:232` |
| `continuous_dist` | `Topology/MetricSpace/Pseudo/Constructions.lean:229` |
| `intermediate_value_uIcc` | `Topology/Order/IntermediateValue.lean:597` |
| `Set.mem_uIcc` | `Order/Interval/Set/UnorderedInterval.lean:208` |

Thus the mathematics is machine-checked (v4.33.1) and the API surface is confirmed
present in the pinned release (v4.17.0). **Before tagging**, produce a genuine
pinned-toolchain compile log on a networked machine:

```bash
# in the v4.17.0 release repo
lake exe cache get && lake build
lake env lean extensions/RACI/AngleTorsion.lean   # expect exit 0, no sorry
```

Record that log alongside `compile-log.txt` and update the SHA-256 if the file
changes. Do **not** present the v4.33.1 log as a v4.17.0 result.

## Files

- `AngleTorsion.lean` — the module (self-contained, `import Mathlib` only).
- `compile-log.txt` — local compile + axiom audit + cross-version API evidence.

SHA-256 (`AngleTorsion.lean`):
`16c1f4792d93bfd728f2c4bb4a3b32b766234c878f628cb0d125724958b9403d`
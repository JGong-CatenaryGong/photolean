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

## mathlib version (pinned verification complete)

The pinned reviewer-facing release uses **Lean v4.17.0 / mathlib rev
`5269898d6a51d047931107c8d72d934d8d5d3753`**. The module has been **machine-checked
under this exact pinned toolchain**: `lake env lean AngleTorsion.lean` exits 0 with
no errors, no warnings and no `sorry`, and every delivered theorem has axiom
footprint exactly `[propext, Classical.choice, Quot.sound]` (see `compile-log.txt`).

The pinned olean cache was materialised in a pure-ASCII-path mirror carrying the
byte-identical `lake-manifest.json` and `lean-toolchain`; the compiled file is
byte-identical to this one (SHA-256 below). Two Windows-specific obstacles were
worked around without affecting the checked file:

1. Windows Schannel `curl` fails the certificate revocation check
   (`CRYPT_E_NO_REVOCATION_CHECK`) and emits a GBK error that Lean's UTF-8
   subprocess reader rejects. `leantar.exe 0.1.14` was fetched with
   `curl --ssl-no-revoke` and placed at the cache path.
2. A temporary `~/.curlrc` (`ssl-no-revoke`) let `lake exe cache get` download the
   6296 cache files (100% success); it was removed after the build.

To reproduce on a networked machine:

```bash
# in the v4.17.0 release repo (use an ASCII path on Windows)
lake exe cache get
lake env lean extensions/RACI/AngleTorsion.lean   # exit 0, no sorry
```

A secondary cross-check under Lean v4.33.1 / mathlib `0df444a` also exits 0 with
the same axiom footprint. The API surface used is stable across both versions:

| API | v4.17.0 source location |
| --- | --- |
| `continuous_subtype_val` | `Topology/Constructions.lean:380` |
| `Continuous.dist` | `Topology/MetricSpace/Pseudo/Constructions.lean:232` |
| `continuous_dist` | `Topology/MetricSpace/Pseudo/Constructions.lean:229` |
| `intermediate_value_uIcc` | `Topology/Order/IntermediateValue.lean:597` |
| `Set.mem_uIcc` | `Order/Interval/Set/UnorderedInterval.lean:208` |

## Files

- `AngleTorsion.lean` — the module (self-contained, `import Mathlib` only).
- `compile-log.txt` — pinned v4.17.0 compile + axiom audit + isolation + reproducibility evidence.

SHA-256 (`AngleTorsion.lean`):
`16c1f4792d93bfd728f2c4bb4a3b32b766234c878f628cb0d125724958b9403d`
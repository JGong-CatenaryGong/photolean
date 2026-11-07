/-
PhotoLean.RelationAudit — umbrella import of the certified relation layer.

This is the only new build target added to `lakefile.toml`; it re-exports the semantic core
(`PhotoLean.RelationAudit.Defs`) and the pilot certificate set (`PhotoLean.RelationAudit.Pilot`).
The pilot includes a proof-relevant conditional-composition chain (Marcus normal region through
the Evans–Polanyi bounds to the absence of an inverted direction) and registers Kasha–Marcus as
a conditional equivalence carrying the `hic` premise rather than as a composition. The layer is
additive: no delivered theory module is imported for modification, and no delivered statement
changes.

There is no unproved placeholder and no custom axiomatic declaration in this layer.
-/
import PhotoLean.RelationAudit.Defs
import PhotoLean.RelationAudit.Pilot

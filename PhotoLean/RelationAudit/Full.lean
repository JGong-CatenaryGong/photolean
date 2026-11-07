/-
PhotoLean.RelationAudit.Full — umbrella import for the R3 migration fragments.

This module is additive. It wires the three disjoint section modules into one
import target so the integration gates can build and elaborate all fragments
together without touching the R1 umbrella `PhotoLean.RelationAudit`, the R1
pilot, the R2 dispositions ledger, or any delivered theory module.

The fragments partition the 41 R2 `certificate-required` declarations:

* `Sections01_05` — 16 rows: kernel definitional pins, §2 equivalences and
  observation-channel bridges, and the §3 one-way implication;
* `Sections06_10` — 6 rows: the §6 Hammond/Marcus equivalence, the §7 kernel
  definitional pin, and four §8 reclassifications;
* `Sections11_17` — 19 rows: §12/§15 kernel and rate definitional pins,
  predicate equivalences, and the §11/§15/§17 reclassifications.

This module deliberately carries no certificate list of its own. The migration
tooling reads `relation_audit/migration/*.json` and generates the kind,
premise-ID, composition-projection and axiom checks from those fragments; a
second hand-maintained list would be able to drift from the fragments.
-/
import PhotoLean.RelationAudit.Full.Sections01_05
import PhotoLean.RelationAudit.Full.Sections06_10
import PhotoLean.RelationAudit.Full.Sections11_17

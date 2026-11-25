import OAI.Hierarchy.FixedMaskAdviceCounting
import OAI.Hierarchy.FixedMaskAdviceBound

namespace OAI
/-! # Fixed mask advice with a linear number of probes -/

namespace Hierarchy.FixedMaskAdvice

open Finset

/-- The fixed advice of CT Section 11.1, indexed by both endpoint residues.
The same strings serve every obstruction set of at most a quarter of the colors. -/
theorem exists_advice {B h : ℕ} (hB : 0 < B) (bound : B ≤ 2^h) :
    ∃ str : (Fin (B^2) × Fin (B^2)) → Fin (8*(4*h+2)) → Fin B,
      ∀ S : Finset (Fin B), 4*S.card ≤ B →
        (univ.filter fun j =>
          8*(4*h+2) ≤ 2*(univ.filter fun k => str j k ∈ S).card).card < B :=
  exists_of_union_bound hB (union_lt_one hB bound)

end Hierarchy.FixedMaskAdvice

end OAI

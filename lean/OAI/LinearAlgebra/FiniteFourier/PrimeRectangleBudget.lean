import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleFreeCounts
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleCounts
import OAI.LinearAlgebra.FiniteFourier.PrimeBatchParameters

/-! # Recursive calls in one routed clock stage -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Classical

/-- Every charged rectangle contributes once per digit and power. The two
endpoint incidence sums are each bounded by the number of labels times the
maximum number of cut patterns at a label. -/
theorem primePencilCalls_bound (ℓ L v m D R : ℕ) [Fact ℓ.Prime] :
    Fintype.card (ZMod ℓ)ˣ * (Fintype.card (ChargedRectangle L v (L / ℓ)) * m * R * (2 * D) +
       R * (∑ r : FreeBitRectangle ℓ L v, (Fintype.card (bitTargets r.val) +
         Fintype.card (bitSources r.val))) * (2 * D)) ≤ primePencilCalls ℓ L v m D R := by
  have hunit : Fintype.card (ZMod ℓ)ˣ ≤ ℓ := by
    simpa using (Fintype.card_le_of_injective Units.val (Units.val_injective (α := ZMod ℓ)))
  have hfree :
      (∑ r : FreeBitRectangle ℓ L v, (Fintype.card (bitTargets r.val) + Fintype.card (bitSources r.val)))
        ≤ (2^v)^L * (1+v)^L + (2^v)^L * (1+v)^L := by
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add (sum_card_freeBitTargets_le ℓ L v) (sum_card_freeBitSources_le ℓ L v)
  calc
    _ ≤ ℓ * ((2^L * (2^v)^(L/ℓ)) * m * R * (2*D) +
      R * ((2^v)^L * (1+v)^L + (2^v)^L * (1+v)^L) * (2*D)) := by
      gcongr
      exact card_chargedRectangle_le L v (L/ℓ)
    _ = _ := by unfold primePencilCalls; ring

end FiniteFourier
end LinearAlgebra
end OAI

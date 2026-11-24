import OAI.Computability.VPVNP.PermanentGraph

/-!
# Weight of a consistent variable ring

Only position `m` of each ring carries the variable weight. Multiplying the
row weights for a consistent choice therefore contributes one factor for
each variable assigned true.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

/-- For consistent ring orientations the product of all row weights is the
weight of the corresponding Boolean assignment. -/
theorem prod_ringWeight {k m : ℕ} {R : Type*} [CommMonoid R] (w : Fin k → R)
    (a : RingRow k m → Bool) (x : Fin k → Bool) (hx : ∀ v j, a (v, j) = x v) :
    (∏ u, ringWeight w u (a u)) = ∏ v, if x v then w v else 1 := by
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro v _
  let j₀ : Fin (m + 2) := ⟨m, by omega⟩
  rw [Finset.prod_eq_single_of_mem j₀ (Finset.mem_univ _)]
  · cases hv : x v <;> simp [ringWeight, ringLabel, hx, hv, j₀]
  · intro j _ hj
    have hval : j.val ≠ m := fun he => hj (Fin.ext he)
    simp [ringWeight, ringLabel, hval]

end PermanentReduction

end VPVNP
end Computability
end OAI

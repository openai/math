import OAI.Computability.VPVNP.GrassmannTypes
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Bounds for normalized Grassmann distance arrays

The means over ordered pairs of fixed type are continuous linear averages.
Nonnegative arrays satisfying the typewise mean bounds of Section 5 have
uniformly bounded entries. This gives a common compact box for the normalized
arrays, even when the target CAT(0) space varies.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

theorem continuous_mean (m r : ℕ) : Continuous (fun D : Plane m → Plane m → ℝ => mean D r) := by
  unfold mean
  apply Continuous.div_const
  exact continuous_finsetSum Finset.univ fun p _ =>
    (continuous_apply p.val.2).comp (continuous_apply p.val.1)

theorem mean_smul {m : ℕ} (D : Plane m → Plane m → ℝ) (r : ℕ) (s : ℝ) :
    mean (fun a b => s * D a b) r = s * mean D r := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

theorem mean_nonneg {m : ℕ} {D : Plane m → Plane m → ℝ}
    (hD : ∀ a b, 0 ≤ D a b) (r : ℕ) : 0 ≤ mean D r := by
  exact div_nonneg (Finset.sum_nonneg fun p _ => hD p.val.1 p.val.2) (Nat.cast_nonneg _)

/-- Every ordered pair has type between zero and the plane dimension. -/
theorem exists_type_le {m : ℕ} (a b : Plane m) : ∃ r ≤ m, HasType r a b := by
  let U := a.val ⊔ b.val
  have hlo : m ≤ Module.finrank (ZMod 2) U := by
    exact a.property.ge.trans (Submodule.finrank_mono le_sup_left)
  have hhi : Module.finrank (ZMod 2) U ≤ 2 * m := by
    simpa only [Space, Module.finrank_pi, Fintype.card_fin] using U.finrank_le
  refine ⟨Module.finrank (ZMod 2) U - m, by omega, ?_⟩
  change Module.finrank (ZMod 2) U = m + (Module.finrank (ZMod 2) U - m)
  omega

theorem exists_coordinate_bound (m : ℕ) :
    ∃ K : ℝ, ∀ D : Plane m → Plane m → ℝ, (∀ a b, 0 ≤ D a b) →
      (∀ r ≤ m, mean D r ≤ r) → ∀ a b, D a b ≤ K := by
  refine ⟨(m : ℝ) * (Fintype.card (Plane m) : ℝ) ^ 2, ?_⟩
  intro D hD hmean a b
  obtain ⟨r, hr, ht⟩ := exists_type_le a b
  let p : Pair m r := ⟨(a, b), ht⟩
  let : Nonempty (Pair m r) := ⟨p⟩
  have hpos : 0 < (Fintype.card (Pair m r) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : Fintype.card (Pair m r) ≤ Fintype.card (Plane m) ^ 2 := by
    simpa only [Fintype.card_prod, pow_two] using
      Fintype.card_le_of_injective (fun x : Pair m r => x.val) Subtype.val_injective
  calc
    D a b ≤ ∑ t : Pair m r, D t.val.1 t.val.2 :=
      Finset.single_le_sum (fun (t : Pair m r) _ => hD t.val.1 t.val.2) (Finset.mem_univ p)
    _ ≤ (r : ℝ) * Fintype.card (Pair m r) := (div_le_iff₀ hpos).mp (hmean r hr)
    _ ≤ _ := mul_le_mul (by exact_mod_cast hr) (by exact_mod_cast hcard) hpos.le (Nat.cast_nonneg _)

end Grassmann

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.MarkedTensor

/-!
# Moving one marked tensor index along an identity wire

Appendix A.2 of *VP and VNP differ over every field* bounds the cost of moving
an index of dimension `q` by `q ^ d(a,b)`. The local maps copy the background
indices, pass the wire endpoint at the destination to the output, and pair the
other endpoint with the marked index at its original party. These operations
also apply when both endpoints are at the same party.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

universe u v w

variable {k : Type u} {J : Type v} [Fintype J]

/-- An identity wire supplies a local restriction moving the marked index
from `b` to `a`, over any commutative semiring. -/
theorem marked_restricts_move [CommSemiring k] (B : J → Type*) [∀ j, Fintype (B j)]
    (I : Type*) [Fintype I] (a b : J) (T : ((j : J) → B j) → I → k) :
    Restricts (tensorProduct (marked B I b T) (wire a b I)) (marked B I a T) := by
  classical
  let L (j : J) (out : B j × (j = a → I))
      (p : (B j × (j = b → I)) × ((j = a → I) × (j = b → I))) : k :=
    if out.1 = p.1.1 ∧ (∀ h, out.2 h = p.2.1 h) ∧ (∀ h, p.1.2 h = p.2.2 h) then 1 else 0
  refine ⟨L, ?_⟩
  funext out
  let i := (out a).2 rfl
  let lift (j : J) : (B j × (j = b → I)) × ((j = a → I) × (j = b → I)) :=
    (((out j).1, fun _ ↦ i), (fun _ ↦ i, fun _ ↦ i))
  simp only [applyLocal, tensorProduct, marked, wire, L, Fintype.prod_boole]
  rw [Finset.sum_eq_single lift]
  · have h : ∀ j : J, (out j).1 = (lift j).1.1 ∧
        (∀ h : j = a, (out j).2 h = (lift j).2.1 h) ∧
        (∀ h : j = b, (lift j).1.2 h = (lift j).2.2 h) :=
      fun _ ↦ ⟨rfl, by rintro rfl; rfl, fun _ ↦ rfl⟩
    rw [ite_eq_left h, ite_eq_left (show (lift a).2.1 rfl = (lift b).2.2 rfl from rfl), mul_one, one_mul]
  · intro x _ hx
    split_ifs with hloc hw
    · exfalso
      apply hx
      have ha : (x a).2.1 rfl = i := ((hloc a).2.1 rfl).symm
      have hb : (x b).2.2 rfl = i := hw.symm.trans ha
      funext j
      refine Prod.ext (Prod.ext ((hloc j).1.symm) ?_) (Prod.ext ?_ ?_)
      · funext h
        subst j
        exact ((hloc b).2.2 rfl).trans hb
      · funext h
        subst j
        exact ha
      · funext h
        subst j
        exact hb
    all_goals simp
  · exact fun h ↦ (h (Finset.mem_univ _)).elim

namespace SpectralPoint

variable [Field k] (F : SpectralPoint k J)
variable (B : J → Type) [∀ j, Fintype (B j)] (I : Type) [Fintype I]
variable (a b : J) (T : ((j : J) → B j) → I → k)

/-- The wire's spectral value bounds the factor required to move a marked index. -/
theorem value_marked_le_wire_mul :
    F.value (marked B I a T) ≤ F.value (wire a b I) * F.value (marked B I b T) := by
  simpa only [F.value_tensorProduct, mul_comm] using F.monotone (marked_restricts_move B I a b T)

/-- The elementary index-moving bound of Appendix A.2. -/
theorem value_marked_move_le [Nonempty I] :
    (F.value (marked B I a T) : ℝ) ≤ (Fintype.card I : ℝ) ^ F.wireDistance a b *
      (F.value (marked B I b T) : ℝ) := by
  have h := NNReal.coe_le_coe.mpr (F.value_marked_le_wire_mul B I a b T)
  rw [NNReal.coe_mul, F.value_wire_equiv a b (Fintype.equivFin I),
    F.value_wire_eq_rpow a b Fintype.card_pos] at h
  exact h

/-- Vanishing of the marked tensor's spectral value is independent of the placement. -/
theorem value_marked_eq_zero_iff :
    F.value (marked B I a T) = 0 ↔ F.value (marked B I b T) = 0 := by
  constructor
  · intro h
    have H := F.value_marked_le_wire_mul B I b a T
    simpa [h] using H
  · intro h
    have H := F.value_marked_le_wire_mul B I a b T
    simpa [h] using H

/-- Moving a marked index between parties at zero wire distance preserves its value. -/
theorem value_marked_eq_of_dist_zero (hab : F.wireDistance a b = 0) :
    F.value (marked B I a T) = F.value (marked B I b T) := by
  rcases isEmpty_or_nonempty I with hI | hI
  · have hz (j : J) : F.value (marked B I j T) = 0 :=
      F.value_zero _ (funext fun x ↦ isEmptyElim ((x j).2 rfl))
    rw [hz, hz]
  · have h₁ := F.value_marked_move_le B I a b T
    have h₂ := F.value_marked_move_le B I b a T
    rw [F.wireDistance_comm b a, hab, Real.rpow_zero, one_mul] at h₂
    rw [hab, Real.rpow_zero, one_mul] at h₁
    exact NNReal.coe_injective (le_antisymm h₁ h₂)

/-- The placement of a one-dimensional marked index has no effect on its value. -/
theorem value_marked_eq_of_card_one (hI : Fintype.card I = 1) :
    F.value (marked B I a T) = F.value (marked B I b T) := by
  have : Nonempty I := Fintype.card_pos_iff.mp (hI ▸ Nat.one_pos)
  have h₁ := F.value_marked_move_le B I a b T
  have h₂ := F.value_marked_move_le B I b a T
  simp only [hI, Nat.cast_one, Real.one_rpow, one_mul] at h₁ h₂
  exact NNReal.coe_injective (le_antisymm h₁ h₂)

end SpectralPoint
end WireTensor

end VPVNP
end Computability
end OAI

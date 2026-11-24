import OAI.Computability.VPVNP.ExteriorLevels
import OAI.Computability.VPVNP.MarkedSplitBound

/-! # Finite exterior bound for a marked tensor

In Appendix A.2 the degree-`h` exterior identity gives two orders of the
creation and contraction operators. Placing the old marked index at opposite
endpoints bounds the two orders by wire costs through degrees `h+1` and `h-1`.
The matrices are the same integral matrices over every field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.SpectralPoint

open ExteriorLevels Lemmata.FockCircuits

/-- The finite, unpowered inequality underlying the relocation estimate in
Lemma A.1. The parties `x`, `a`, and `b` may coincide. -/
theorem value_marked_exterior_bound {k J : Type*} [Field k] [Fintype J]
    (F : SpectralPoint k J) (B : J → Type) [∀ j, Fintype (B j)] {Q h : ℕ}
    (hh : 1 ≤ h) (hQ : h < Q) (x a b : J) (T : ((j : J) → B j) → Fin Q → k) :
    (F.value (marked B (Fin Q) x T) : ℝ) * (Q.choose h : ℝ) ^ F.wireDistance a b ≤
      F.value (marked B (Fin Q) b T) * (Q.choose h : ℝ) ^ F.wireDistance a x *
        (Q.choose (h + 1) : ℝ) ^ F.wireDistance x b +
      F.value (marked B (Fin Q) a T) * (Q.choose (h - 1) : ℝ) ^ F.wireDistance a x *
        (Q.choose h : ℝ) ^ F.wireDistance x b := by
  classical
  have : Nonempty (Fin Q) := ⟨⟨0, by omega⟩⟩
  have level_nonempty (r : ℕ) (hr : r ≤ Q) : Nonempty (Level Q r) :=
    Fintype.card_pos_iff.mp (by simpa only [card_level] using Nat.choose_pos hr)
  have : Nonempty (Level Q h) := level_nonempty h hQ.le
  have : Nonempty (Level Q (h + 1)) := level_nonempty _ hQ
  have : Nonempty (Level Q (h - 1)) := level_nonempty _ (by omega)
  let createUp (i : Fin Q) (α : Level Q h) (z : Level Q (h + 1)) : k :=
    entry ℤ (Fock.create ℤ i) z α
  let contractDown (j : Fin Q) (β : Level Q h) (z : Level Q (h + 1)) : k :=
    entry ℤ (Fock.contract ℤ j) β z
  let contractLow (j : Fin Q) (α : Level Q h) (z : Level Q (h - 1)) : k :=
    entry ℤ (Fock.contract ℤ j) z α
  let createBack (i : Fin Q) (β : Level Q h) (z : Level Q (h - 1)) : k :=
    entry ℤ (Fock.create ℤ i) β z
  let P i j β α := ∑ z, createUp i α z * contractDown j β z
  let M i j β α := ∑ z, contractLow j α z * createBack i β z
  have hcar (i j : Fin Q) (β α : Level Q h) : P i j β α + M i j β α =
      if i = j ∧ β = α then 1 else 0 := by
    simpa only [P, M, createUp, contractDown, contractLow, createBack, mul_comm] using
      int_matrix_car k i j β α
  have hsplit := NNReal.coe_le_coe.mpr
    (value_marked_wire_le_split F B (Fin Q) (Level Q h) x a b T P M (fun i j β α ↦ by
      by_cases he : i = j ∧ β = α <;> simpa only [he, ite_true, ite_false] using hcar i j β α))
  rw [NNReal.coe_mul, NNReal.coe_add, F.value_wire_equiv a b (Fintype.equivFin (Level Q h)),
    F.value_wire_eq_rpow a b Fintype.card_pos, card_level] at hsplit
  have hp := F.value_splitMarkedTerm_le_plus B (Fin Q) (Level Q h) (Level Q (h + 1))
    x a b b T P createUp contractDown (fun _ _ _ _ ↦ rfl)
  have hm := F.value_splitMarkedTerm_le_minus B (Fin Q) (Level Q h) (Level Q (h - 1))
    x a b a T M contractLow createBack (fun _ _ _ _ ↦ rfl)
  simpa only [card_level, F.wireDistance_self, F.wireDistance_comm b x, Real.rpow_zero,
    one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using hsplit.trans (add_le_add hp hm)

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI

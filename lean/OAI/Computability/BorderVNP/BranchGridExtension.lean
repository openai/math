import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! # A common finite field for branch choices

The fixed points of an iterated Frobenius give an extension inside the specified
algebraically closed field. Its cardinality can be chosen between the forbidden
degree and that degree times the ground-field cardinality.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

variable (E₀ K : Type*) [Field E₀] [Fintype E₀] [Field K] [Algebra E₀ K]

/-- The field of constants in the algebraic closure fixed by the indicated Frobenius power. -/
noncomputable def gridExtension (m : ℕ) : IntermediateField E₀ K where
  __ := ((FiniteField.frobeniusAlgHom E₀ K ^ m).toRingHom).eqLocusField (RingHom.id K)
  algebraMap_mem' x := (FiniteField.frobeniusAlgHom E₀ K ^ m).commutes x

/-- Membership in the grid extension is tested by a single Frobenius equation. -/
theorem mem_gridExtension {m : ℕ} (x : K) :
    x ∈ gridExtension E₀ K m ↔ x ^ (Fintype.card E₀ ^ m) = x := by
  change (FiniteField.frobeniusAlgHom E₀ K ^ m) x = x ↔ _
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

/-- There are exactly `|E₀|^m` elements in the fixed field for `m > 0`. -/
theorem card_gridExtension [IsAlgClosed K] {m : ℕ} (hm : m ≠ 0) :
    Nat.card (gridExtension E₀ K m) = Fintype.card E₀ ^ m := by
  classical
  let g := (Polynomial.X ^ (Fintype.card E₀ ^ m) - Polynomial.X : Polynomial E₀)
  have hne : g ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero E₀ hm Fintype.one_lt_card
  obtain ⟨p, hp, k, _, hcard⟩ := FiniteField.card' E₀
  let := hp
  have hdiv : p ∣ Fintype.card E₀ ^ m := by
    rw [hcard, ← pow_mul]
    exact dvd_pow_self _ (Nat.mul_ne_zero k.pos.ne' hm)
  have hroots : Fintype.card (g.rootSet K) = Fintype.card E₀ ^ m := by
    rw [Polynomial.card_rootSet_eq_natDegree (galois_poly_separable p _ hdiv)
      (IsAlgClosed.splits _)]
    exact FiniteField.X_pow_card_pow_sub_X_natDegree_eq E₀ hm Fintype.one_lt_card
  have hset : (↑(gridExtension E₀ K m) : Set K) = g.rootSet K := by
    ext x
    rw [SetLike.mem_coe, mem_gridExtension, Polynomial.mem_rootSet_of_ne hne]
    simp [g, sub_eq_zero]
  calc
    Nat.card (gridExtension E₀ K m) = Nat.card (g.rootSet K) := by
      change Nat.card (↑(gridExtension E₀ K m) : Set K) = _
      rw [hset]
    _ = _ := (Nat.card_eq_fintype_card).trans hroots

/-- A finite extension inside the ambient closure whose size exceeds the degree budget.
Its size increases by at most one factor of `|E₀|` beyond that budget. -/
theorem exists_gridExtension [IsAlgClosed K] (D : ℕ) :
    ∃ E : IntermediateField E₀ K, Finite E ∧
      D < Nat.card E ∧ Nat.card E ≤ Fintype.card E₀ * max D 1 := by
  let q := Fintype.card E₀
  let m := Nat.log q D + 1
  let E := gridExtension E₀ K m
  have hc : Nat.card E = q ^ m := card_gridExtension E₀ K (Nat.succ_ne_zero _)
  have hd : D < q ^ m := Nat.lt_pow_succ_log_self Fintype.one_lt_card D
  refine ⟨E, (Nat.card_pos_iff.mp (hc ▸ Nat.zero_lt_of_lt hd)).2, hc ▸ hd, ?_⟩
  rw [hc, show m = Nat.log q D + 1 from rfl, pow_succ', ← show Fintype.card E₀ = q from rfl]
  gcongr
  rcases D with _ | d
  · simp
  · exact (Nat.pow_log_le_self q (Nat.succ_ne_zero _)).trans (le_max_left ..)

/-- A singly exponential degree bound needs only its bit length plus the ground-field
bit length to encode each chosen constant. -/
theorem size_grid_card_le {D e q : ℕ} (h : e ≤ q * max D 1) :
    e.size ≤ q.size + (max D 1).size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact h.trans_lt <| Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self q)
    (Nat.lt_size_self (max D 1)).le (Nat.two_pow_pos _)

end Branch

end BorderVNP
end Computability
end OAI

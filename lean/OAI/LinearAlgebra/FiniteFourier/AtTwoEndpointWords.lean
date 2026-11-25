import OAI.LinearAlgebra.FiniteFourier.AtTwoEndpointPivot
import OAI.LinearAlgebra.FiniteFourier.SemilocalBorderShear
import OAI.LinearAlgebra.FiniteFourier.TransvectionLayer

/-! # Bounded words for the small semilocal blocks of the prime-axis transforms

Applying a unit pivot one row at a time gives a uniform quadratic bound for arbitrary
invertible matrices. Both endpoint maps use this bound only in dimensions at most three.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]

omit [Finite (MaximalSpectrum R)] in
private theorem border_word {n : ℕ} {M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R}
    (hs : ∀ x : R, ∃ t, IsUnit t ∧ IsUnit (x - t))
    (hM : ∃ l : List (TransvectionStruct (Fin n ⊕ Unit) R),
      l.length ≤ n ∧ (l.map TransvectionStruct.toMatrix).prod = M) : LayerWord (6*n) M := by
  obtain ⟨l, hl, rfl⟩ := hM
  apply LayerWord.pad (Nat.mul_le_mul_left 6 hl)
  clear hl
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm (6*l.length) 6,
      List.map_cons, List.prod_cons]
    exact layerWord_mul (layerWord_transvection_of_unit_split hs t.hij t.c) ih

/-- A dimension-uniform semilocal elimination bound in monomial/shear slots.
For the prime-axis conversion one uses dimensions two and three. -/
theorem layerWord_semilocal_isUnit
    (hs : ∀ x : R, ∃ t, IsUnit t ∧ IsUnit (x - t))
    {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I R) (hM : IsUnit M) :
    LayerWord (9 * Fintype.card I ^ 2 + 1) M := by
  classical
  suffices ∀ n, Fintype.card I = n → LayerWord (9*n^2+1) M from this _ rfl
  intro n hn
  induction n generalizing I with
  | zero =>
    have h : IsEmpty I := Fintype.card_eq_zero_iff.mp hn
    have he : M = 1 := Subsingleton.elim _ _
    subst M
    exact layerWord_one _
  | succ n ih =>
    let e : I ≃ Fin n ⊕ Unit := Fintype.equivOfCardEq (by simp [hn])
    let N := reindexAlgEquiv R R e M
    obtain ⟨v, b, c, S, s, hS, he⟩ := semilocal_matrix_pivot N
      (hM.map (reindexAlgEquiv R R e))
    have hwordS := ih S hS (Fintype.card_fin n)
    have hdiag : LayerWord 1 (diagonal fun _ : Unit => (s : R)) :=
      layerWord_of_layer (layerMatrix_diagonal_units fun _ => s.isUnit)
    have hmid := layerWord_parallel hwordS (hdiag.pad (by omega))
    have h₁ := border_word hs (exists_border_lower_transvections v)
    have h₂ := border_word hs (exists_border_upper_transvections b)
    have h₃ := border_word hs (exists_border_lower_transvections c)
    have h := layerWord_mul h₁ (layerWord_mul (layerWord_mul h₂ hmid) h₃)
    rw [← he] at h
    have h' := h.relabel e.symm
    have he' : N.submatrix e e = M := by ext i j; simp [N, coe_reindexAlgEquiv]
    simp only [Equiv.symm_symm, he'] at h'
    apply h'.pad
    nlinarith only [Nat.zero_le n]

end FiniteFourier
end LinearAlgebra
end OAI

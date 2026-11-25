import OAI.LinearAlgebra.SpectralBooks.Fermion.WickOrder
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickKernel
import OAI.LinearAlgebra.SpectralBooks.Fermion.Pascal

/-! # The full contractions in the fermionic crossing identity

In a complete matching the first field must be contracted. Removing this
field and its partner is precisely the minor occurring in Laplace expansion.
The signs from moving past fields of the left block total a triangular number.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open scoped BigOperators

variable {α k : Type*} [CommRing k]

/-- Scalar contribution of the Wick matchings with no unmatched fields. -/
def fullContractions (κ : α → α → k) (l r : List α) : k :=
  ∑ p : Matching l r, if p.residual.isEmpty then p.weight κ else 0

theorem fullContractions_cons (κ : α → α → k) (x : α) (l r : List α) :
    fullContractions κ (x :: l) r =
      ∑ j : Fin r.length, ((-1 : k) ^ l.length * ((-1 : k) ^ j.val * κ x r[j.val])) *
        fullContractions κ l (r.eraseIdx j.val) := by
  unfold fullContractions
  change (∑ p : Matching l r ⊕ (Σ j : Fin r.length, Matching l (r.eraseIdx j.val)), _) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp [Matching.residual, Matching.weight, Finset.mul_sum, mul_ite]

private theorem eraseIdx_ofFn {n : ℕ} (r : Fin (n+1) → α) (j : Fin (n+1)) :
    (List.ofFn r).eraseIdx j.val = List.ofFn (fun t ↦ r (j.succAbove t)) := by
  have hj : j.val < (List.ofFn r).length := by simpa using j.isLt
  apply List.ext_getElem
  · rw [List.length_eraseIdx_of_lt hj, List.length_ofFn, List.length_ofFn]; omega
  · intro i hi hi'
    have hin : i < n := by simpa using hi'
    let t : Fin n := ⟨i,hin⟩
    by_cases h : i < j.val
    · rw [List.getElem_eraseIdx_of_lt hi h]
      simp only [List.getElem_ofFn]
      exact congrArg r (j.succAbove_of_castSucc_lt t h).symm
    · rw [List.getElem_eraseIdx_of_ge hi (Nat.le_of_not_gt h)]
      simp only [List.getElem_ofFn]
      exact congrArg r (j.succAbove_of_le_castSucc t (Nat.le_of_not_gt h)).symm

private theorem fullContractions_step (κ : α → α → k) {n : ℕ}
    (l r : Fin (n+1) → α) :
    fullContractions κ (List.ofFn l) (List.ofFn r) =
      ∑ j : Fin (n+1), ((-1 : k)^n * ((-1 : k)^j.val * κ (l 0) (r j))) *
        fullContractions κ (List.ofFn (fun t ↦ l t.succ)) (List.ofFn (fun t ↦ r (j.succAbove t))) := by
  rw [List.ofFn_succ (f := l), fullContractions_cons]
  apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := r)))
  intro j
  let s : Fin (n+1) := ⟨j.val, by simpa using j.isLt⟩
  simp only [List.length_ofFn, List.getElem_ofFn]
  rw [show (List.ofFn r).eraseIdx j.val = List.ofFn (fun t ↦ r (s.succAbove t)) from
    eraseIdx_ofFn r s]
  rfl

/-- Complete matchings contribute the determinant of the matrix of pairings,
with one sign for each interchange in interleaving the two blocks. -/
theorem fullContractions_eq_det (κ : α → α → k) (n : ℕ) (l r : Fin n → α) :
    fullContractions κ (List.ofFn l) (List.ofFn r) =
      (-1 : k) ^ n.choose 2 * (Matrix.of (fun i j ↦ κ (l i) (r j))).det := by
  induction n with
  | zero =>
    rw [Matrix.det_isEmpty, Nat.choose_eq_zero_of_lt (by decide : 0 < 2), pow_zero, mul_one]
    change (∑ _ : Unit, (1 : k)) = 1
    simp
  | succ n ih =>
    rw [fullContractions_step, Matrix.det_succ_row_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, pow_add, Matrix.of_apply]
    rw [show (Matrix.of (fun i j ↦ κ (l i) (r j))).submatrix Fin.succ j.succAbove =
      Matrix.of (fun i s ↦ κ (l i.succ) (r (j.succAbove s))) from rfl]
    ring

private theorem sorted_ofFn (S : Finset ℕ) {n : ℕ} (h : S.card = n) :
    S.sort (· ≤ ·) = List.ofFn (S.orderEmbOfFin h) := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi'
    simp [Finset.orderEmbOfFin_apply]

/-- For two equal-cardinality occupation states, the scalar from the full
contractions is the manuscript's signed integral Pascal minor. -/
theorem fullContractions_kernelNumerator (I J : Finset ℕ) (h : J.card = I.card) :
    fullContractions kernelNumerator (I.sort (· ≤ ·)) (J.sort (· ≤ ·)) = pairing I J := by
  rw [sorted_ofFn I rfl, sorted_ofFn J h, fullContractions_eq_det]
  let A : Matrix (Fin I.card) (Fin I.card) ℤ :=
    Matrix.of (fun i j ↦ ((I.orderEmbOfFin rfl i + J.orderEmbOfFin h j).choose
      (I.orderEmbOfFin rfl i) : ℤ))
  let v (i : Fin I.card) : ℤ := (-1) ^ I.orderEmbOfFin rfl i
  change _ * (Matrix.of (fun i j ↦ v i * A i j)).det = _
  rw [Matrix.det_mul_column, pairing, stateMinor, dite_eq_left h, pairingSign, pow_add]
  have hs : (∑ i : Fin I.card, I.orderEmbOfFin rfl i) = ∑ i ∈ I, i := by
    conv_rhs => rw [← I.map_orderEmbOfFin_univ rfl]
    rw [Finset.sum_map]; rfl
  change _ * ((∏ i, (-1 : ℤ) ^ I.orderEmbOfFin rfl i) * A.det) = _ * A.det
  rw [Finset.prod_pow_eq_pow_sum, hs, mul_assoc]

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.Fermion.WickOrder
import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionFactor

/-! # Pole orders of partial Wick contractions

A matched pair of derivative orders `i,j` contributes `i+j+1` poles.
Each unmatched field has strictly positive doubled energy, so a partial
matching of equal-size lists loses at least one pole.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

variable {α : Type*}

/-- Doubled energy of a list of possibly labeled differentiated fields. -/
def wordWeight (mode : α → ℕ) (l : List α) : ℕ := (l.map (fun x ↦ 2 * mode x + 1)).sum

theorem wordWeight_eq (mode : α → ℕ) (l : List α) :
    wordWeight mode l = 2 * (l.map mode).sum + l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

private theorem wordWeight_erase (mode : α → ℕ) (l : List α) (j : Fin l.length) :
    wordWeight mode (l.eraseIdx j.val) + (2 * mode l[j.val] + 1) = wordWeight mode l := by
  induction l with
  | nil => exact Fin.elim0 j
  | cons x l ih =>
    cases j using Fin.cases with
    | zero => simp [wordWeight, Nat.add_comm]
    | succ k =>
      have h := ih k
      simp only [wordWeight, List.map_cons, List.sum_cons, Fin.val_succ,
        List.eraseIdx_cons_succ, List.getElem_cons_succ] at *
      omega

namespace Matching

/-- Total Laurent pole order for the pairs in a Wick matching. -/
def poleOrder (mode : α → ℕ) : {l r : List α} → Matching l r → ℕ
  | [], _, _ => 0
  | _ :: _, _, .inl p => poleOrder mode p
  | x :: _, r, .inr ⟨j, p⟩ => mode x + mode r[j.val] + 1 + poleOrder mode p

/-- Matched and unmatched fields partition the doubled energy exactly. -/
theorem twice_poleOrder_add_residual (mode : α → ℕ) (l r : List α) (p : Matching l r) :
    2 * p.poleOrder mode + wordWeight mode p.residual = wordWeight mode l + wordWeight mode r := by
  induction l generalizing r with
  | nil => simp [poleOrder, residual, wordWeight]
  | cons x l ih =>
    rcases p with p | ⟨j, p⟩
    · have h := ih r p
      simp only [poleOrder, residual, wordWeight, List.map_cons, List.sum_cons] at *
      omega
    · have h := ih _ p
      have h' := wordWeight_erase mode r j
      simp only [poleOrder, residual, wordWeight, List.map_cons, List.sum_cons] at *
      omega

/-- The cleared order kills an incomplete contraction of two equally large blocks. -/
theorem poleOrder_le_of_residual_ne_nil (mode : α → ℕ) {l r : List α}
    (p : Matching l r) (hlr : l.length = r.length) (hp : p.residual ≠ []) :
    p.poleOrder mode ≤ order (wordWeight mode l) (wordWeight mode r) := by
  have h := p.twice_poleOrder_add_residual mode ..
  rw [wordWeight_eq, wordWeight_eq mode l, wordWeight_eq mode r] at h
  have hn : 0 < p.residual.length := List.length_pos_iff.mpr hp
  simp only [order, wordWeight_eq]
  omega

/-- A full contraction of two nonempty equal-size blocks leaves one pole. -/
theorem poleOrder_eq_of_residual_nil (mode : α → ℕ) {l r : List α}
    (p : Matching l r) (hlr : l.length = r.length) (hl : l ≠ []) (hp : p.residual = []) :
    p.poleOrder mode = order (wordWeight mode l) (wordWeight mode r) + 1 := by
  have h := p.twice_poleOrder_add_residual mode ..
  rw [hp] at h
  have hn : 0 < l.length := List.length_pos_iff.mpr hl
  simp only [show wordWeight mode [] = 0 from rfl, add_zero, wordWeight_eq] at h
  simp only [order, wordWeight_eq]
  omega

end Matching
end Fermion

end SpectralBooks
end LinearAlgebra
end OAI

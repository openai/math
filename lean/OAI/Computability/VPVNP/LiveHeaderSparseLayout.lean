import OAI.Computability.VPVNP.LiveAuxiliaryHeaders
import Mathlib.Tactic.FinCases

/-!
# Dense iteration over the sparse auxiliary header

A cursor visits the three cut lengths, the two primed group indices, the
advice, both exterior cuts and the nominations. The destination skips the
unused capacity after each exterior field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveAuxiliaryHeaders

open PrimedInputRAM

/-- Cumulative starts, ending with the exact count of populated words. -/
def rangeStart (L : Lengths) (labels : ℕ) : Fin 8 → ℕ :=
  ![0, 3, 3+L.index, 3+2*L.index, exteriorBase L, exteriorBase L+L.leftCut,
    exteriorBase L+L.leftCut+L.rightCut, exteriorBase L+L.leftCut+L.rightCut+labels]

/-- The number of words actually visited by the auxiliary copy sweep over all seven input
fields. -/
def populated (L : Lengths) (labels : ℕ) := rangeStart L labels 7

/-- Offsets in the virtual machine's actual header, including capacity holes. -/
def destinationStart (L : Lengths) : Fin 7 → ℕ :=
  ![0, 3, 3+L.index, 3+2*L.index, exteriorBase L, exteriorBase L+L.cutCapacity, Header.count L]

private theorem starts_monotone (L : Lengths) (N : ℕ) : Monotone (rangeStart L N) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  fin_cases i <;> simp [rangeStart, exteriorBase]
  omega

private theorem hasRange (L : Lengths) (N : ℕ) (i : Fin (populated L N)) :
    ∃ j : Fin 7, rangeStart L N j.castSucc ≤ i.val ∧ i.val < rangeStart L N j.succ := by
  by_contra! h
  have hb (j : Fin 8) : rangeStart L N j ≤ i.val := by
    induction j using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ j ih => exact h j ih
  exact i.isLt.not_ge (hb 7)

/-- The descriptor containing a packed cursor; the RAM dispatcher performs the
corresponding seven comparisons directly. -/
noncomputable def rangeAt (L : Lengths) (N : ℕ) (i : Fin (populated L N)) : Fin 7 :=
  (hasRange L N i).choose

theorem rangeAt_bounds (L : Lengths) (N : ℕ) (i : Fin (populated L N)) :
    rangeStart L N (rangeAt L N i).castSucc ≤ i.val ∧ i.val < rangeStart L N (rangeAt L N i).succ :=
  (hasRange L N i).choose_spec

theorem rangeAt_skips (L : Lengths) (N : ℕ) (i : Fin (populated L N)) (j : Fin 7)
    (h : j < rangeAt L N i) : rangeStart L N j.succ ≤ i.val :=
  (starts_monotone L N (by change j.val + 1 ≤ (rangeAt L N i).val; exact h)).trans
    (rangeAt_bounds L N i).1

theorem rangeEnd_le (L : Lengths) (N : ℕ) (j : Fin 7) :
    rangeStart L N j.succ ≤ populated L N := starts_monotone L N (Fin.le_last _)

/-- Map a dense copy cursor to its shadow offset, skipping unused exterior capacity before the
next field. -/
def sparseOffset (L : Lengths) (N : ℕ) (i : Fin (populated L N)) : Fin (span L N) :=
  let left := exteriorBase L + L.leftCut
  let right := left + L.rightCut
  ⟨if i.val < left then i.val else if i.val < right then
    exteriorBase L + L.cutCapacity + (i.val-left) else Header.count L + (i.val-right), by
    have hi : i.val < exteriorBase L + L.leftCut + L.rightCut + N := i.isLt
    have := L.leftFit
    have := L.rightFit
    by_cases hl : i.val < left <;> by_cases hr : i.val < right <;>
      simp only [hl, hr, ite_true, ite_false] <;>
      dsimp only [right, left, exteriorBase, span, Header.count] at * <;> omega⟩

theorem sparseOffset_at_range (L : Lengths) (N : ℕ) (i : Fin (populated L N)) :
    (sparseOffset L N i).val = destinationStart L (rangeAt L N i) +
      (i.val - rangeStart L N (rangeAt L N i).castSucc) := by
  have h := rangeAt_bounds L N i
  generalize he : rangeAt L N i = j at h ⊢
  by_cases hl : i.val < exteriorBase L + L.leftCut <;>
    by_cases hr : i.val < exteriorBase L + L.leftCut + L.rightCut <;>
    simp only [sparseOffset, hl, hr, ite_true, ite_false] <;>
    fin_cases j <;> norm_num [rangeStart, destinationStart, exteriorBase] at h hl hr ⊢ <;> omega

theorem sparseOffset_range (L : Lengths) (N : ℕ) (j : Fin (span L N)) :
    j ∈ cells L N ↔ ∃ i : Fin (populated L N), sparseOffset L N i = j := by
  have hleft := L.leftFit
  have hright := L.rightFit
  have hj : j.val < Header.count L + N := j.isLt
  rw [mem_cells]
  constructor
  · rintro (h | ⟨h₁,h₂⟩ | h)
    · refine ⟨⟨j.val, ?_⟩, ?_⟩
      · change j.val < exteriorBase L + L.leftCut + L.rightCut + N
        omega
      · exact Fin.ext (ite_eq_left h)
    · let v := exteriorBase L + L.leftCut + (j.val - (exteriorBase L + L.cutCapacity))
      have lo : exteriorBase L + L.leftCut ≤ v := by dsimp [v]; omega
      have hi : v < exteriorBase L + L.leftCut + L.rightCut := by dsimp [v]; omega
      refine ⟨⟨v, (hi.trans_le (Nat.le_add_right ..))⟩, Fin.ext ?_⟩
      simp only [sparseOffset, ite_eq_right lo.not_gt, ite_eq_left hi, v]
      omega
    · let v := exteriorBase L + L.leftCut + L.rightCut + (j.val - Header.count L)
      have lo : exteriorBase L + L.leftCut + L.rightCut ≤ v := by dsimp [v]; omega
      have hi : v < exteriorBase L + L.leftCut + L.rightCut + N := by dsimp [v]; omega
      refine ⟨⟨v, hi⟩, Fin.ext ?_⟩
      simp only [sparseOffset, ite_eq_right lo.not_gt, ite_eq_right (by omega : ¬v < exteriorBase L + L.leftCut), v]
      omega
  · rintro ⟨i,rfl⟩
    by_cases hl : i.val < exteriorBase L + L.leftCut
    · exact Or.inl (by simpa only [sparseOffset, ite_eq_left hl] using hl)
    · by_cases hr : i.val < exteriorBase L + L.leftCut + L.rightCut
      · refine Or.inr (Or.inl ?_)
        simp only [sparseOffset, ite_eq_right hl, ite_eq_left hr]
        omega
      · refine Or.inr (Or.inr ?_)
        simp only [sparseOffset, ite_eq_right hl, ite_eq_right hr]
        omega

end LiveAuxiliaryHeaders

end VPVNP
end Computability
end OAI

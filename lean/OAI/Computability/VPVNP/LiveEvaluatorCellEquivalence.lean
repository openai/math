import OAI.Computability.VPVNP.LiveEvaluatorStep

/-!
# Equivalence of the scheduled cell comparisons with a tape transition

The private RAM visits old cells in increasing order. A one-cell move
permutes the output positions cyclically and pairs the old discarded
endpoint with the new blank endpoint. The extra blank check on that old
endpoint makes this exactly the unbounded-tape move.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorStep

open UniversalMachine LiveEvaluatorEncoding RAMTape

variable {M : ℕ}

/-- The destination paired with old cell `i` in the RAM scan. -/
def cellDestination (move : Symbol) (i : WindowCell M) : WindowCell M :=
  if move = 0 then i
  else if move = 1 then
    if h : i.val = 2 * M then ⟨0, by omega⟩ else ⟨i.val + 1, by have := i.isLt; omega⟩
  else if i.val = 0 then ⟨2 * M, by omega⟩ else ⟨i.val - 1, by omega⟩

/-- Whether a nonstationary tape move clips this old cell at the boundary of the finite window. -/
def cellClipped (move : Symbol) (i : WindowCell M) : Prop :=
  move ≠ 0 ∧ (if move = 1 then i.val = 2 * M else i.val = 0)

instance (move : Symbol) (i : WindowCell M) : Decidable (cellClipped move i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The symbol after writing at the head position, using the previous symbol at every other
cell. -/
def writtenSymbol (t : TapeWindow M) (write : Symbol) (i : WindowCell M) : Symbol :=
  if i.val = M then write else t.cells i

theorem cellDestination_surjective (move : Symbol) : Function.Surjective (cellDestination (M := M) move) := by
  intro j
  fin_cases move
  · exact ⟨j, rfl⟩
  · by_cases h : j.val = 0
    · exact ⟨⟨2 * M, by omega⟩, by apply Fin.ext; simp [cellDestination, h]⟩
    · exact ⟨⟨j.val - 1, by omega⟩, by
        apply Fin.ext
        simp [cellDestination, show j.val - 1 ≠ 2 * M by omega]
        omega⟩
  · by_cases h : j.val = 2 * M
    · exact ⟨⟨0, by omega⟩, by apply Fin.ext; simp [cellDestination, h]⟩
    · exact ⟨⟨j.val + 1, by omega⟩, by apply Fin.ext; simp [cellDestination]⟩

private theorem updatedCell_at_index (t : TapeWindow M) (write move : Symbol) (j : ℤ)
    (i : WindowCell M) (h : j + moveDelta move = (i.val : ℤ) - M) :
    updatedCell t write move j = writtenSymbol t write i := by
  simp only [updatedCell, h, TapeWindow.read_index, writtenSymbol]
  by_cases hi : i.val = M <;> simp [hi, show ((i.val : ℤ) - M = 0) ↔ i.val = M by omega]

private theorem updatedCell_far (t : TapeWindow M) (write move : Symbol) (j : ℤ)
    (h : j + moveDelta move < -(M : ℤ) ∨ (M : ℤ) < j + moveDelta move) :
    updatedCell t write move j = 0 := by
  rw [updatedCell, ite_eq_right (by omega), TapeWindow.read, dite_eq_right (by omega)]

private theorem shifted_eq_source (t : TapeWindow M) (write move : Symbol) (i : WindowCell M) :
    (updatedWindow t write move).cells (cellDestination move i) =
      if cellClipped move i then 0 else writtenSymbol t write i := by
  change updatedCell t write move ((↑(cellDestination move i).val : ℤ) - M) = _
  fin_cases move <;> simp [cellClipped, cellDestination]
  · apply updatedCell_at_index; simp
  · split
    next h => apply updatedCell_far; simp
    next h => apply updatedCell_at_index; simp; omega
  · split
    next h => apply updatedCell_far; simp; omega
    next h =>
      apply updatedCell_at_index
      have hi : 0 < i.val := by simpa [Nat.pos_iff_ne_zero] using h
      simp [Int.ofNat_sub (show 1 ≤ i.val from hi)]; omega

theorem boundaryBlank_iff_clipped (t : TapeWindow M) (write move : Symbol) :
    boundaryBlank t write move = true ↔
      ∀ i : WindowCell M, cellClipped move i → writtenSymbol t write i = 0 := by
  let lo : WindowCell M := ⟨0, by omega⟩
  let hi : WindowCell M := ⟨2 * M, by omega⟩
  fin_cases move
  · change boundaryBlank t write 0 = true ↔ ∀ i, cellClipped 0 i → writtenSymbol t write i = 0
    have h₁ := updatedCell_far t write 0 (-(M : ℤ) - 1) (by simp)
    have h₂ := updatedCell_far t write 0 ((M : ℤ) + 1) (by simp)
    simp [boundaryBlank, h₁, h₂, cellClipped]
  · change boundaryBlank t write 1 = true ↔ ∀ i, cellClipped 1 i → writtenSymbol t write i = 0
    have h₁ := updatedCell_far t write 1 (-(M : ℤ) - 1) (by simp; omega)
    have h₂ := updatedCell_at_index t write 1 ((M : ℤ) + 1) hi (by simp [hi]; omega)
    simp only [boundaryBlank, decide_eq_true_eq, h₁, true_and, h₂]
    constructor
    · intro h i hc
      have he : i = hi := Fin.ext (by simpa [cellClipped, hi] using hc)
      exact he ▸ h
    · exact fun h => h hi (by simp [cellClipped, hi])
  · change boundaryBlank t write 2 = true ↔ ∀ i, cellClipped 2 i → writtenSymbol t write i = 0
    have h₁ := updatedCell_at_index t write 2 (-(M : ℤ) - 1) lo (by simp [lo])
    have h₂ := updatedCell_far t write 2 ((M : ℤ) + 1) (by simp; omega)
    simp only [boundaryBlank, decide_eq_true_eq, h₁, h₂, and_true]
    constructor
    · intro h i hc
      have he : i = lo := Fin.ext (by simpa [cellClipped, lo] using hc)
      exact he ▸ h
    · exact fun h => h lo (by simp [cellClipped, lo])

/-- The RAM comparison at every old cell is equivalent to both the exterior
blank guard and the complete equality of the proposed output tape. -/
theorem cellChecks_iff (old out : TapeWindow M) (write move : Symbol) :
    (∀ i : WindowCell M,
      (cellClipped move i → writtenSymbol old write i = 0) ∧
        out.cells (cellDestination move i) = writtenSymbol old write i) ↔
      boundaryBlank old write move = true ∧ out = updatedWindow old write move := by
  rw [boundaryBlank_iff_clipped]
  constructor
  · intro h
    refine ⟨fun i => (h i).1, TapeWindow.ext ?_⟩
    funext j
    obtain ⟨i, rfl⟩ := cellDestination_surjective move j
    rw [(h i).2, shifted_eq_source]
    split
    · exact (h i).1 ‹_›
    · rfl
  · rintro ⟨h, rfl⟩ i
    refine ⟨h i, ?_⟩
    rw [shifted_eq_source]
    split
    · exact (h i ‹_›).symm
    · rfl

end LiveEvaluatorStep

end VPVNP
end Computability
end OAI

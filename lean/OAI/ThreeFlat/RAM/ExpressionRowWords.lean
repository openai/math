import OAI.ThreeFlat.MaterializeMemory
import OAI.ThreeFlat.BlankNetwork
import OAI.ThreeFlat.RAM.ExpressionContraction

namespace OAI
/-! # Verifying a descriptor one native cell record at a time -/

namespace ThreeFlat.RAM.GeneratedContraction

open Computability.VPVNP.BurstRAM BitLayout DescriptorScan Contraction BitNetwork Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {p w : ℕ}

/-- Input pins, zero hidden bits, zero cell rows, the fixed field table, and
a separately generated source segment. Only the sizes of the destination
network are used to lay out these words. -/
noncomputable def inputMemory (pins hidden cells : ℕ) (code : FieldCode F w)
    (pin : Fin pins → Bool) (source : Memory w) : Memory w :=
  fillSegment (cellsBase pins hidden) (11*cells) (fun _ => 0)
    (memoryWithTail source (blankNetwork pins hidden cells) code pin (fun _ => false))

theorem inputMemory_outside (N : BitNetwork F p) (code : FieldCode F w) (pin : Fin p → Bool)
    (source : Memory w) {a : ℕ} (ha : a < footprint N)
    (away : a < cellsBase p N.internal ∨ mulBase p N.internal N.cells ≤ a) :
    inputMemory p N.internal N.cells code pin source a = memory N code pin (fun _ => false) a := by
  have h : ¬(cellsBase p N.internal ≤ a ∧ a < cellsBase p N.internal+11*N.cells) := by
    unfold mulBase at away
    omega
  simp only [inputMemory, fillSegment, ite_eq_right h]
  exact (memoryWithTail_agrees (blankNetwork p N.internal N.cells) code pin (fun _ => false)
    source a ha).trans (blankNetwork_read N code pin (fun _ => false) a ha away)

theorem inputMemory_source (N : BitNetwork F p) (code : FieldCode F w) (pin : Fin p → Bool)
    (source : Memory w) (j : ℕ) :
    inputMemory p N.internal N.cells code pin source (footprint N+j) = source j := by
  have h : ¬(cellsBase p N.internal ≤ footprint N+j ∧
      footprint N+j < cellsBase p N.internal+11*N.cells) := by
    unfold footprint mulBase
    omega
  simp only [inputMemory, fillSegment, ite_eq_right h]
  exact memoryWithTail_after (blankNetwork p N.internal N.cells) code pin (fun _ => false) source j

/-- Below the external source, only the literal one, the input pins, and the
fixed field multiplication table can need initialization. -/
theorem inputMemory_support (N : BitNetwork F p) (code : FieldCode F w) (pin : Fin p → Bool)
    (source : Memory w) {a : ℕ} (ha : a < footprint N)
    (nz : inputMemory p N.internal N.cells code pin source a ≠ 0) :
    a = 1 ∨ (2 ≤ a ∧ a < hiddenBase p) ∨ mulBase p N.internal N.cells ≤ a := by
  by_cases last : mulBase p N.internal N.cells ≤ a
  · exact Or.inr (Or.inr last)
  by_cases row : cellsBase p N.internal ≤ a
  · have inrow : cellsBase p N.internal ≤ a ∧ a < cellsBase p N.internal + 11*N.cells :=
      ⟨row, Nat.lt_of_not_ge last⟩
    exact False.elim (nz (by simp [inputMemory, fillSegment, inrow]))
  have before := Nat.lt_of_not_ge row
  rw [inputMemory_outside N code pin source ha (Or.inl before)] at nz
  by_cases lit : a < 2
  · rcases (by omega : a = 0 ∨ a = 1) with rfl | h
    · exact False.elim (nz ((read_source N code pin (fun _ => false) (.constant false)).trans rfl))
    · exact Or.inl h
  by_cases hp : a < hiddenBase p
  · exact Or.inr (Or.inl ⟨by omega, hp⟩)
  · let j : Fin N.internal := ⟨a-hiddenBase p, by unfold cellsBase at before; omega⟩
    have eq : sourceAddress (.hidden j : BitSource N.internal p) = a := by
      change hiddenBase p+(a-hiddenBase p) = a
      omega
    rw [← eq] at nz
    exact False.elim (nz ((read_source N code pin (fun _ => false) (.hidden j)).trans rfl))

/-- To certify every physical descriptor word it suffices to compute the
three source addresses and the eight coefficients for each numbered cell.
The input memory may change within the generated interval. -/
theorem descriptor_correct_of_rows (N : BitNetwork F p) (fit : Fits N w)
    (pin : Fin p → Bool) (hidden : Fin N.internal → Bool) (input : Memory w)
    (word : Word w → Memory w → Word w)
    (row : ∀ (i : RowAddress N.cells) (m : Memory w),
      agreesOutside (cellsBase p N.internal) (mulBase p N.internal N.cells) m input →
      word (rowLocation (cellsBase p N.internal) i : Word w) m =
        cellRows (N.sourceWords w) N.table (codec N fit).encode i) :
    ∀ (a : Word w) (m : Memory w), cellsBase p N.internal ≤ a.val →
      a.val < mulBase p N.internal N.cells →
      agreesOutside (cellsBase p N.internal) (mulBase p N.internal N.cells) m input →
      word a m = memory N (codec N fit) pin hidden a.val := by
  intro a m lo hi contents
  obtain ⟨i, eq⟩ := exists_rowLocation lo hi
  have address : (rowLocation (cellsBase p N.internal) i : Word w) = a := by
    rw [eq]
    exact Fin.cast_val_eq_self a
  calc
    word a m = word (rowLocation (cellsBase p N.internal) i : Word w) m := by rw [address]
    _ = _ := row i m contents
    _ = memory N (codec N fit) pin hidden (rowLocation (cellsBase p N.internal) i) :=
      (read_row_slot N _ _ _ i).symm
    _ = _ := congrArg (memory N (codec N fit) pin hidden) eq

end ThreeFlat.RAM.GeneratedContraction

end OAI

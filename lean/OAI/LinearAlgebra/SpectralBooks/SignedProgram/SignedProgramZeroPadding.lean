import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramOrder

/-! # Checking unused one-hot cells -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram.Hot
open SignedMachine
open private blankMove blankRow from OAI.LinearAlgebra.SpectralBooks.SignedProgramPadding
open private reconstructRow reconstructRow_value from OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramCells
open private Move.normal Row.normal pad from OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramLocal

private theorem move_normal_val {n : ℕ} (k : Fin (n+1)) (m : Move n) (c : MoveCell n) :
    c.value (Move.normal m k) = if c.active k then c.value m else 0 := by
  cases c with
  | write i | direction i =>
    by_cases h : i.val < k.val <;> simp [Move.normal,pad,MoveCell.value,MoveCell.active,h,symbolCode,directionCode]
  | _ => rfl

private theorem move_blank_val {n : ℕ} (c : MoveCell n) : c.value (blankMove n) = 0 := by cases c <;> rfl

private theorem row_blank_val {n : ℕ} (c : RowCell n) : c.value (blankRow n) = 0 := by
  cases c with
  | move b c => exact move_blank_val _
  | _ => rfl

private theorem row_normal_val {n : ℕ} (k : Fin (n+1)) (r : Row n) (c : RowCell n) :
    c.value (Row.normal r k) = if c.active k r.kind then c.value r else 0 := by
  cases c with
  | state | input | kind => rfl
  | read i =>
    by_cases h : i.val < k.val <;> simp [Row.normal,pad,RowCell.value,RowCell.active,h,symbolCode]
  | out =>
    by_cases h : r.kind = 0 <;> simp [Row.normal,RowCell.value,RowCell.active,h,outputCode]
  | move b c =>
    simp only [Row.normal,RowCell.value,RowCell.active]
    generalize r.kind = tag
    fin_cases tag <;> cases b <;> simp [move_blank_val,move_normal_val]

theorem zeroPadding_iff {n : ℕ} (t : Table n) :
    (∀ c : Cell n, c.active t = false → c.value t = 0) ↔ t.Canonical := by
  rw [← localPadding_iff]
  constructor
  · intro hz i
    have hval (c : RowCell n) : c.value (t.row i) =
        c.value (if i.val < t.rows.val then Row.normal (t.row i) t.tapes else blankRow n) := by
      by_cases h : i.val < t.rows.val
      · rw [ite_eq_left h, row_normal_val]
        by_cases ha : c.active t.tapes (t.row i).kind = true
        · simp [ha]
        · simp only [ite_eq_right ha]
          exact hz (.row i c) (by simp [Cell.active,h,ha])
      · rw [ite_eq_right h, row_blank_val]
        exact hz (.row i c) (by simp [Cell.active,h])
    exact (reconstructRow_value (t.row i)).symm.trans
        ((congrArg (reconstructRow n) (funext hval)).trans (reconstructRow_value _))
  · intro h c hc
    cases c with
    | tapes | rows => contradiction
    | row i c =>
      change c.value (t.row i) = 0
      have he := h i
      by_cases hi : i.val < t.rows.val
      · have ha : c.active t.tapes (t.row i).kind = false := by simpa [Cell.active,hi] using hc
        rw [ite_eq_left hi] at he
        exact (congrArg (fun r ↦ c.value r) he).trans (by rw [row_normal_val]; simp [ha])
      · rw [ite_eq_right hi] at he
        rw [he, row_blank_val]

end SignedProgram.Hot

end SpectralBooks
end LinearAlgebra
end OAI

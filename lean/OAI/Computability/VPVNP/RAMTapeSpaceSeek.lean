import OAI.Computability.VPVNP.RAMTapeSpaceTravel
import OAI.Computability.VPVNP.RAMTapeStackControl

/-!
# Physical head displacement during a stack seek and rewind

Passing a packed cell advances the first head by one and moves the second
head left by two to store the cell and its tag. Restoring the cell reverses
both movements. These counts include blank stack delimiters.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine

variable {k : ℕ} {Q : Type*} (code : StackCode (Fin k) Q)

private theorem scanCellTravel (q : Q) (i : Fin (k+1)) (hi : i.val ≠ 0) (x : Symbol)
    (data saved : List Symbol) :
    Travel (rows code) 3 1 (-2) (.seek q i) (tapeList (x :: data)) (tapeList (scratch saved))
      (.seek q (remaining i x)) (tapeList data) (tapeList (scratch (x :: saved))) := by
  apply Travel.cons (dx := 0) (dy := -1) (show rows code (.seek q i) (tapeList (x :: data)).head
    (tapeList (scratch saved)).head = .one (.next (.stash q (remaining i x) x) 0 2
    (tapeList (scratch saved)).head 1) by simp [rows, hi])
  simp only [pop_cell, left_for_push]
  apply Travel.cons (d := 0) (e := 1) (dx := 0) (dy := 0) rfl
  simp only [update_stay, write_left]
  apply Travel.cons (d := 0) (e := 0) (dx := 0) (dy := 0) rfl
  simp only [update_stay, replace_top]
  exact .nil ..

private theorem scanFieldTravel (q : Q) (i : Fin (k+1)) (hi : i.val ≠ 0) (s : List Bool)
    (data saved : List Symbol) :
    Travel (rows code) (3 * (s.length + 1)) (s.length + 1) (-2 * (s.length + 1))
      (.seek q i) (tapeList (s.map bit ++ 0 :: data)) (tapeList (scratch saved))
      (.seek q (remaining i 0)) (tapeList data) (tapeList (scratch (0 :: (s.map bit).reverse ++ saved))) := by
  induction s generalizing saved with
  | nil => exact scanCellTravel code q i hi 0 data saved
  | cons b s ih =>
    have hcell := scanCellTravel code q i hi (bit b) (s.map bit ++ 0 :: data) saved
    have hbit : remaining i (bit b) = i := by cases b <;> simp [bit, remaining]
    rw [hbit] at hcell
    have h := hcell.trans (ih (bit b :: saved))
    convert h using 1 <;> simp [List.append_assoc] <;> omega

/-- The seek moves one packed cell right and two scratch cells left for
every cell of the prefix. -/
theorem seek_travel (q : Q) (ss : List (List Bool)) (hs : ss.length ≤ k) (data saved : List Symbol) :
    Travel (rows code) (3 * (fields ss).length) (fields ss).length (-2 * (fields ss).length)
      (.seek q ⟨ss.length, by omega⟩) (tapeList (fields ss ++ data)) (tapeList (scratch saved))
      (.seek q 0) (tapeList data) (tapeList (scratch ((fields ss).reverse ++ saved))) := by
  induction ss generalizing saved with
  | nil => exact .nil ..
  | cons s ss ih =>
    let i : Fin (k+1) := ⟨ss.length+1, by simp only [List.length_cons] at hs; omega⟩
    have hr : remaining i 0 = ⟨ss.length, by simp at hs; omega⟩ := by
      apply Fin.ext
      simp [remaining, i]
    have hfield := scanFieldTravel code q i (by simp [i]) s (fields ss ++ data) saved
    rw [hr] at hfield
    have htail := ih (by simp at hs; omega) (0 :: (s.map bit).reverse ++ saved)
    convert hfield.trans htail using 1 <;> simp [List.append_assoc] <;> omega

private theorem restoreCellTravel (q : Q) (x : Symbol) (xs data : List Symbol) :
    Travel (rows code) 3 (-1) 2 (.restore q) (tapeList data) (tapeList (scratch (x :: xs)))
      (.restore q) (tapeList (x :: data)) (tapeList (scratch xs)) := by
  simp only [scratch, List.flatMap_cons, List.cons_append, List.nil_append]
  apply Travel.cons (d := 0) (e := 2) (dx := -1) (dy := 1) rfl
  simp only [update_stay, pop_cell]
  apply Travel.cons (d := 1) (e := 2) (dx := 0) (dy := 0) rfl
  simp only [left_for_push, pop_cell]
  apply Travel.cons (d := 0) (e := 0) (dx := 0) (dy := 0) rfl
  simp only [replace_top, update_stay, cells_head]
  exact .nil ..

/-- Rewind all saved cells to their original order, returning the scratch
head to its original position. The final empty test moves neither head. -/
theorem restore_travel (q : Q) (saved data : List Symbol) :
    Travel (rows code) (3 * saved.length + 1) (- (saved.length : ℤ)) (2 * saved.length)
      (.restore q) (tapeList data) (tapeList (scratch saved)) (.ready q)
      (tapeList (saved.reverse ++ data)) (tapeList []) := by
  induction saved generalizing data with
  | nil =>
    change Travel (rows code) 1 0 0 (.restore q) (tapeList data) (tapeList []) (.ready q) (tapeList data) (tapeList [])
    apply Travel.cons (d := 0) (e := 0) (dx := 0) (dy := 0) rfl
    rw [update_stay]
    exact .nil ..
  | cons x xs ih =>
    have h := (restoreCellTravel code q x xs data).trans (ih (x :: data))
    convert h using 1 <;> simp [List.append_assoc] <;> omega

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI

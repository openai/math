import OAI.Computability.VPVNP.RAMTapeStackControl

/-!
# Seeking an addressed bit stack

The finite counter counts delimiters. Every saved cell, including an internal
blank, takes exactly three physical transitions and two scratch cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.StackCompiler

open UniversalMachine

variable {k : ℕ} {Q : Type*} (code : StackCode (Fin k) Q)

private theorem scan_cell (q : Q) (i : Fin (k+1)) (hi : i.val ≠ 0) (x : Symbol)
    (data saved : List Symbol) :
    Runs (rows code) 3 (.seek q i) (tapeList (x :: data)) (tapeList (scratch saved))
      (.seek q (remaining i x)) (tapeList data) (tapeList (scratch (x :: saved))) := by
  apply Runs.cons (show rows code (.seek q i) (tapeList (x :: data)).head
    (tapeList (scratch saved)).head = .one (.next (.stash q (remaining i x) x) 0 2
    (tapeList (scratch saved)).head 1) by simp [rows, hi])
  simp only [pop_cell, left_for_push]
  apply Runs.cons rfl
  simp only [update_stay, write_left]
  apply Runs.cons rfl
  simp only [update_stay, replace_top]
  exact .nil ..

private theorem scan_field (q : Q) (i : Fin (k+1)) (hi : i.val ≠ 0) (s : List Bool)
    (data saved : List Symbol) :
    Runs (rows code) (3 * (s.length + 1)) (.seek q i) (tapeList (s.map bit ++ 0 :: data))
      (tapeList (scratch saved)) (.seek q (remaining i 0)) (tapeList data)
      (tapeList (scratch (0 :: (s.map bit).reverse ++ saved))) := by
  induction s generalizing saved with
  | nil => exact scan_cell code q i hi 0 data saved
  | cons b s ih =>
    have hcell := scan_cell code q i hi (bit b) (s.map bit ++ 0 :: data) saved
    have hbit : remaining i (bit b) = i := by cases b <;> simp [bit, remaining]
    rw [hbit] at hcell
    have h := hcell.trans (ih (bit b :: saved))
    simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, List.append_assoc] using h

/-- The target stack follows the explicitly listed prefix of stacks. -/
theorem seek_run (q : Q) (ss : List (List Bool)) (hs : ss.length ≤ k) (data saved : List Symbol) :
    Runs (rows code) (3 * (fields ss).length) (.seek q ⟨ss.length, by omega⟩)
      (tapeList (fields ss ++ data)) (tapeList (scratch saved))
      (.seek q 0) (tapeList data) (tapeList (scratch ((fields ss).reverse ++ saved))) := by
  induction ss generalizing saved with
  | nil => exact .nil ..
  | cons s ss ih =>
    let i : Fin (k+1) := ⟨ss.length+1, by simp only [List.length_cons] at hs; omega⟩
    have hr : remaining i 0 = ⟨ss.length, by simp at hs; omega⟩ := by
      apply Fin.ext
      simp [remaining, i]
    have hfield := scan_field code q i (by simp [i]) s (fields ss ++ data) saved
    rw [hr] at hfield
    have htail := ih (by simp at hs; omega) (0 :: (s.map bit).reverse ++ saved)
    simpa [i, Nat.mul_add, Nat.mul_succ, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hfield.trans htail

end RAMTape.StackCompiler

end VPVNP
end Computability
end OAI

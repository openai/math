import OAI.Computability.VPVNP.RAMTapeBoundaryControl
import OAI.Computability.VPVNP.RAMTapeBoundaryDecision

/-!
# Scanning the five fields of a boundary record

The same field subroutine serves both the adjacent-row check and the outgoing
edge check. After the fifth return the saved stack contains the whole current
record in reverse order, ready for restoration as the next predecessor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Boundary

open RAMBoundary

/-- In row mode the right stream is the remaining block. In edge mode it is
the outgoing message. The other stream is left untouched by the field pass. -/
def recordView (m : Mode) (left right other width widthBack saved slots : List Bool) : Stacks Port :=
  match m with
  | .row => store right left other width widthBack saved slots
  | .edge => store other left right width widthBack saved slots

private theorem install_recordView (m : Mode) (left right other width widthBack saved slots : List Bool) :
    installStacks (fieldPorts m) (recordView m [] [] other [] [] [] slots)
      (Field.store width widthBack left right saved) =
    recordView m left right other width widthBack saved slots := by
  funext k
  by_cases hk : ∃ j, fieldPorts m j = k
  · obtain ⟨j, rfl⟩ := hk
    rw [installStacks_at (fieldPorts_injective m)]
    cases m <;> cases j <;> rfl
  · rw [installStacks_outside _ _ (not_exists.mp hk)]
    cases m <;> cases k <;> first
      | rfl
      | exact (hk ⟨.left, rfl⟩).elim
      | exact (hk ⟨.right, rfl⟩).elim
      | exact (hk ⟨.width, rfl⟩).elim
      | exact (hk ⟨.widthBack, rfl⟩).elim
      | exact (hk ⟨.saved, rfl⟩).elim

private theorem field_fold (j : Fin 5) (f : Flags) (xs ys : List Bool) :
    Field.fold (stepField j) f xs ys = foldField j f xs ys := by
  induction xs generalizing f ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => exact ih _ _

private theorem field_run (hasPrev hasNext : Bool) (m : Mode) (j : Fin 5) (ok : Bool)
    (f : Flags) {w : ℕ} (a b : RawSlot w) (leftTail rightTail other saved slots : List Bool) :
    StackRuns (code hasPrev hasNext) (7*w+3) (.field m j ok (.tick f))
      (recordView m (BurstRAM.wordBits (a j) ++ leftTail) (BurstRAM.wordBits (b j) ++ rightTail)
        other (List.replicate w true) [] saved slots)
      (afterField m j ok (foldField j f (BurstRAM.wordBits (a j)) (BurstRAM.wordBits (b j))))
      (recordView m leftTail rightTail other (List.replicate w true) []
        ((BurstRAM.wordBits (b j)).reverse ++ saved) slots) := by
  have h := Field.runs (stepField j) f (BurstRAM.wordBits (a j)) (BurstRAM.wordBits (b j))
    leftTail rightTail saved (by simp)
  have linked := h.lift (target := code hasPrev hasNext) (fieldPorts m) (fieldPorts_injective m)
    (.field m j ok) (recordView m [] [] other [] [] [] slots) (by
      intro q hq
      cases q <;> first | rfl | contradiction)
  simp only [BurstRAM.length_wordBits, install_recordView, field_fold] at linked
  exact linked.trans (.cons (.goto rfl) (.nil ..))

private theorem recordBytes_fields {w : ℕ} (a : RawSlot w) :
    recordBytes a = BurstRAM.wordBits (a 0) ++ (BurstRAM.wordBits (a 1) ++
      (BurstRAM.wordBits (a 2) ++ (BurstRAM.wordBits (a 3) ++ BurstRAM.wordBits (a 4)))) := by
  rw [recordBytes, recordWords, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
    List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

/-- A whole record takes five field scans, including one continuation jump
per field. The last continuation chooses the check for the active mode. -/
theorem record_run (hasPrev hasNext : Bool) (m : Mode) (ok : Bool) {w : ℕ}
    (a b : RawSlot w) (leftTail rightTail other saved slots : List Bool) :
    StackRuns (code hasPrev hasNext) (5 * (7*w+3)) (.field m 0 ok (.tick initial))
      (recordView m (recordBytes a ++ leftTail) (recordBytes b ++ rightTail)
        other (List.replicate w true) [] saved slots)
      (.restoreSlot m (ok && if m = .row then checked (foldRecord a b) else equalChecked (foldRecord a b)))
      (recordView m leftTail rightTail other (List.replicate w true) []
        ((recordBytes b).reverse ++ saved) slots) := by
  let n := 7*w+3
  rw [show 5 * (7*w+3) = n + (n + (n + (n + n))) by omega]
  simp only [recordBytes_fields, List.append_assoc, List.reverse_append, foldRecord,
    show List.finRange 5 = [0, 1, 2, 3, 4] from rfl, foldFields]
  refine (field_run hasPrev hasNext m 0 ok initial a b _ _ other saved slots).trans ?_
  refine (field_run hasPrev hasNext m 1 ok _ a b _ _ other _ slots).trans ?_
  refine (field_run hasPrev hasNext m 2 ok _ a b _ _ other _ slots).trans ?_
  refine (field_run hasPrev hasNext m 3 ok _ a b _ _ other _ slots).trans ?_
  exact field_run hasPrev hasNext m 4 ok _ a b leftTail rightTail other _ slots

end RAMTape.Boundary

end VPVNP
end Computability
end OAI

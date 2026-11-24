import OAI.Computability.VPVNP.UniversalMachine

/-!
# Scanning the input tape of the universal coefficient machine

Moving the head preserves the input. After scanning the program prefix, the cell
at offset `i` contains the symbol encoding the `i`th payload bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace QueryTape

open Turing

/-- Input tape with its head at cell `pos`, counting from the first input bit. -/
def atPosition (input : List Bool) (pos : ℕ) : Tape (Fin 3) :=
  (Tape.move Dir.right)^[pos] (Tape.mk₁ (input.map fun b => if b then 2 else 1))

theorem atPosition_zero (input : List Bool) :
    atPosition input 0 = Tape.mk₁ (input.map fun b => if b then 2 else 1) := rfl

theorem move_right_atPosition (input : List Bool) (pos : ℕ) :
    (atPosition input pos).move .right = atPosition input (pos + 1) :=
  (Function.iterate_succ_apply' _ _ _).symm

theorem move_left_atPosition_succ (input : List Bool) (pos : ℕ) :
    (atPosition input (pos + 1)).move .left = atPosition input pos := by
  rw [← move_right_atPosition, Tape.move_right_left]

private theorem head_atPosition (input : List Bool) (pos : ℕ) :
    (atPosition input pos).head = (input.map fun b => if b then 2 else 1).getI pos := by
  simp only [atPosition, Tape.move_right_n_head, Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat,
    ListBlank.nth_mk]

theorem head_atPosition_of_lt (input : List Bool) (pos : ℕ) (hp : pos < input.length) :
    (atPosition input pos).head = if input[pos] then 2 else 1 := by
  rw [head_atPosition, List.getI_eq_getElem _ (by simpa using hp), List.getElem_map]

theorem head_atPosition_length (input : List Bool) :
    (atPosition input input.length).head = 0 := by
  rw [head_atPosition, List.getI_eq_default _ (by simp)]
  rfl

theorem head_atPosition_suffix {k : ℕ} (pre : List Bool) (x : Fin k → Bool) (i : Fin k) :
    (atPosition (pre ++ List.ofFn x) (pre.length + i.val)).head = if x i then 2 else 1 := by
  rw [head_atPosition_of_lt _ _ (by simp),
    List.getElem_append_right (by omega)]
  simp

end QueryTape

end VPVNP
end Computability
end OAI

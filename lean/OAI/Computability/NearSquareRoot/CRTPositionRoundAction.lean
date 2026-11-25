import OAI.Computability.NearSquareRoot.CRTPositionFixedSchedule
import OAI.Computability.NearSquareRoot.CRTPositionLayerTable

/-! # One native round on three equal chunks

The six unordered chunk pairs determine a fixed sequence of native word
operations. Cross-chunk pairs exchange their matched bits with three XORs.
A diagonal pair borrows a distinct chunk and restores all of its bits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.NativeRound

/-- Auxiliary chunk for the three diagonal pairs. -/
def auxiliary (c : Fin 3) : Fin 3 := if c = 0 then 1 else 0

theorem auxiliary_ne (c : Fin 3) : auxiliary c ≠ c := by
  by_cases h : c = 0
  · subst c
    decide
  · simpa [auxiliary,h] using Ne.symm h

/-- Execute the native word operator for a single chunk pair. -/
def stage {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (q : Fin 3 × Fin 3) (w : Fin k → Bool) : Fin k → Bool :=
  if q.1 = q.2 then borrowWord v hv q.1 (auxiliary q.1) w else crossWord v q.1 q.2 w

/-- All six operations on a full native word. -/
def bulkAction {k : ℕ} (v : Equiv.Perm (Fin k)) (hv : Function.Involutive v)
    (w : Fin k → Bool) : Fin k → Bool :=
  FixedSchedule.pairs.foldl (fun word q => stage v hv q word) w

private def tag {m : ℕ} (x : Fin (3*m)) : Fin 3 := (chunkOf x).getD 0

private theorem chunk_eq_tag {m : ℕ} (x : Fin (3*m)) : chunkOf x = some (tag x) := by
  unfold tag chunkOf
  cases h : threeChunksWithTail (3*m) x with
  | inl p => rfl
  | inr j => exact False.elim (by have := j.isLt; omega)

private theorem stage_eq {m : ℕ} (v : Equiv.Perm (Fin (3*m))) (hv : Function.Involutive v)
    (q : Fin 3 × Fin 3) (w : Fin (3*m) → Bool) :
    stage v hv q w = w ∘ FixedSchedule.restrict v hv tag q.1 q.2 := by
  rcases q with ⟨s,d⟩
  funext x
  by_cases h : s=d
  · subst d
    simp only [stage,ite_true,borrowWord_value,chunk_eq_tag,Option.some.injEq,Function.comp_apply,
      FixedSchedule.restrict_apply,or_self]
    split <;> rfl
  · simp only [stage,ite_eq_right h,crossWord_value v hv s d h,chunk_eq_tag,Option.some.injEq,
      Function.comp_apply,FixedSchedule.restrict_apply]
    split <;> rfl

/-- Executing the three cross-chunk and three borrowed-chunk native operators
in schedule order implements the specified involution on every bit. -/
theorem bulkAction_value {m : ℕ} (v : Equiv.Perm (Fin (3*m))) (hv : Function.Involutive v)
    (w : Fin (3*m) → Bool) : bulkAction v hv w = w ∘ v := by
  unfold bulkAction
  simp_rw [stage_eq]
  exact FixedSchedule.word_action v hv tag w

end Controlled.NativeRound

end NearSquareRoot
end Computability
end OAI

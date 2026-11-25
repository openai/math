import OAI.Computability.IntegerMultiplication.SM.Stack

/-!
# Positions of compiled stack-machine heads

The P192 stack compiler keeps the bottom (the address just beyond the last
symbol) fixed, even when an empty stack is popped. Thus restoring a stack
also restores its physical tape and head. A time bound on one call confines
the heads throughout that call, so successive calls can reuse the same cells.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication
open IntegerMultiplication.SM
open IntegerMultiplication.TM (Tape)

variable {A Q I : Type}

private theorem action_bottom (a : Action A) (T : Tape (Option A)) (s : List A)
    (h : T.view = display s) :
    let S := T.apply (a.first (T.view 0))
    (S.apply (a.second (S.view 0))).pos + ((a.perform s).length : ℤ) =
      T.pos + (s.length : ℤ) := by
  cases a <;> cases s <;>
    simp [Tape.apply, Action.first, Action.second, Action.perform, h, TM.Move.shift] <;> omega

/-- Simulate a stack machine, preserving the absolute bottom address of every stack. -/
theorem simulateWithBottom {m : Rule A Q I} {x y : Config A Q I} {n : ℕ}
    (run : Trace (advance m) x n y) (T : I → Tape (Option A)) (repr : faithful x.stack T) :
    ∃ T', faithful y.stack T' ∧
      (∀ i, (T' i).pos + ((y.stack i).length : ℤ) =
        (T i).pos + ((x.stack i).length : ℤ)) ∧
      Trace (TM.advance (toTM m)) ⟨.inl x.pc, T⟩ (2*n) ⟨.inl y.pc, T'⟩ := by
  induction run generalizing T with
  | nil x =>
    exact ⟨T, repr, fun _ => rfl, by simp only [Nat.mul_zero]; exact Trace.nil _⟩
  | @cons x u y n step _ ih =>
    cases op : m x.pc (tops x) with
    | none => simp [advance, op] at step
    | some cmds =>
      simp only [advance, op, Option.map_some, Option.some.injEq] at step
      subst u
      let first : I → Tape (Option A) := fun i => (T i).apply ((cmds.2 i).first ((T i).view 0))
      let next : I → Tape (Option A) := fun i =>
        (first i).apply ((cmds.2 i).second ((first i).view 0))
      have read_tops : (fun i => (T i).view 0) = tops x := by
        funext i
        rw [repr, display_top]
        rfl
      have move₁ : TM.advance (toTM m) ⟨.inl x.pc, T⟩ = some ⟨.inr cmds, first⟩ := by
        simp [TM.advance, toTM, read_tops, op, first]
      have move₂ : TM.advance (toTM m) ⟨.inr cmds, first⟩ = some ⟨.inl cmds.1, next⟩ := rfl
      obtain ⟨T', end_repr, bottom, suffix⟩ := ih next fun i =>
        (cmds.2 i).represent_perform (T i) (x.stack i) (repr i)
      refine ⟨T', end_repr, fun i => (bottom i).trans
        (action_bottom (cmds.2 i) (T i) (x.stack i) (repr i)), ?_⟩
      rw [show 2 * (1 + n) = 1 + (1 + 2 * n) by omega]
      exact .cons move₁ (.cons move₂ suffix)

/-- When two endpoints have the same stack and bottom, both the tape contents and the
head position agree at the endpoints. -/
theorem tape_eq_of_stack_restored {s t : List A} {S T : Tape (Option A)}
    (hs : S.view = display s) (ht : T.view = display t)
    (bottom : S.pos + (s.length : ℤ) = T.pos + (t.length : ℤ)) (restored : s = t) :
    S = T := by
  subst t
  have p : S.pos = T.pos := by omega
  cases S
  cases T
  simp_all

/-- Displacement of any physical head over any trace (in particular over any prefix). -/
theorem head_excursion {m : TM.Rule A Q I} {x y : TM.Config A Q I} {t : ℕ}
    (run : Trace (TM.advance m) x t y) (i : I) :
    (x.tape i).pos - (t : ℤ) ≤ (y.tape i).pos ∧
      (y.tape i).pos ≤ (x.tape i).pos + (t : ℤ) := by
  induction run with
  | nil => simp
  | @cons x z y t step _ ih =>
    cases op : m x.pc (fun j => (x.tape j).view 0) with
    | none => simp [TM.advance, op] at step
    | some cmds =>
      simp only [TM.advance, op, Option.map_some, Option.some.injEq] at step
      subst z
      have : -1 ≤ (cmds.2 i).2.shift ∧ (cmds.2 i).2.shift ≤ 1 := by
        cases (cmds.2 i).2 <;> decide
      dsimp [Tape.apply] at ih
      omega

end NearSquareRoot
end Computability
end OAI

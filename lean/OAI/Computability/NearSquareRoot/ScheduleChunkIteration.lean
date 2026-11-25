import Mathlib.Tactic.Ring
import OAI.Computability.IntegerMultiplication.Code.Repeat
import OAI.Computability.IntegerMultiplication.Code.Auto

/-!
# Iterating costed passes without storing a unary count of passes

The stopping test is computed from the current state on tape. The number of
passes appears only in the proof. This lets two short digit counters drive
quadratically many digit-product calls while retaining their separate sizes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkIteration

open IntegerMultiplication IntegerMultiplication.Code

variable {P S : Type} [Codec S]

/-- A common program with a data-dependent stopping test runs through each of
the prescribed rows of states. Its running time is at most a fixed constant
times the total of the stated bounds for the passes and their stop tests. -/
theorem task {length allowance : P → ℕ} {state : P → ℕ → S}
    (stop : S → Bool) (hs : Easy stop)
    (recognizes : ∀ p t, t ≤ length p → stop (state p t) = decide (t = length p))
    (small : ∀ p t, t ≤ length p → size (state p t) ≤ allowance p)
    (pass : Task (fun v : (p : P) × Fin (length p) => allowance v.1)
      (fun v => send (state v.1 v.2.val)) (fun v => send (state v.1 (v.2.val+1)))) :
    Task (fun p => (length p + 1) * (2 * allowance p + 1))
      (fun p => send (state p 0)) (fun p => send (state p (length p))) := by
  let Pos := (p : P) × Fin (length p + 1)
  let last (v : Pos) := decide (v.2.val = length v.1)
  let advance (v : Pos) : Option Pos :=
    if h : v.2.val < length v.1 then some ⟨v.1, ⟨v.2.val+1, by omega⟩⟩ else none
  let entry (v : Pos) := send (state v.1 v.2.val)
  let exit (v : Pos) := send (state v.1 (length v.1))
  let reply (v : Pos) := match advance v with
    | none => Tree.fork (.atom false) (exit v)
    | some w => Tree.fork (.atom true) (entry w)
  have test : Easy (fun s : S => (stop s,s)) := hs.pair Easy.identity
  have tag : Task (fun v : Pos => allowance v.1) entry
      (fun v => Tree.fork (.atom (last v)) (entry v)) := by
    have h := (test.on (fun v : Pos => state v.1 v.2.val)).mono
      (fun v => small _ _ (Nat.le_of_lt_succ v.2.isLt))
    refine h.conform (fun _ => rfl) (fun _ => rfl) ?_
    intro v
    change Tree.fork (.atom (stop (state v.1 v.2.val))) _ = _
    rw [recognizes _ _ (Nat.le_of_lt_succ v.2.isLt)]
  have select : Task (fun v : Pos => allowance v.1)
      (fun v => Tree.fork (.atom (last v)) (entry v)) reply := by
    apply Task.control last
    · let src (a : {v : Pos // last v = false}) : (p : P) × Fin (length p) := by
        refine ⟨a.val.1, ⟨a.val.2.val, ?_⟩⟩
        have h := a.property
        have := a.val.2.isLt
        simp [last] at h
        omega
      have h := (pass.on src).compose (Task.tag true _)
      refine h.conform (fun _ => by simp [src]) (fun _ => rfl) ?_
      intro v
      have hlt := (src v).2.isLt
      simp [reply,advance,src,entry,show v.val.2.val < length v.val.1 from hlt]
    · have h := Task.tag false (fun v : {v : Pos // last v = true} => entry v.val)
      refine (h.mono (b' := fun v => allowance v.val.1) (fun _ => Nat.zero_le _)).conform
        (fun _ => rfl) (fun _ => rfl) ?_
      intro v
      have he : v.val.2.val = length v.val.1 := by simpa [last] using v.property
      simp [reply,advance,he,entry,exit]
  let pot (v : Pos) := (length v.1 + 1 - v.2.val) * (2 * allowance v.1 + 1)
  have hloop := Task.iterate (a := fun v : Pos => allowance v.1 + allowance v.1)
    (b := pot) (p := entry) (f := exit) advance (tag.compose select) (by
      intro v w e
      dsimp only [advance] at e
      split at e
      · cases e; rfl
      · cases e) (by
      intro v
      dsimp only [advance, pot]
      split
      · next h =>
        simp only [Option.elim_some]
        have e : length v.1+1-v.2.val = (length v.1+1-(v.2.val+1))+1 := by omega
        rw [e]
        apply le_of_eq
        ring
      · next h =>
        have he : v.2.val = length v.1 := by have := v.2.isLt; omega
        simp [he]; omega)
  simpa [entry,exit,pot] using hloop.on (fun p => (⟨p,⟨0,by omega⟩⟩ : Pos))

end ChunkIteration

end NearSquareRoot
end Computability
end OAI

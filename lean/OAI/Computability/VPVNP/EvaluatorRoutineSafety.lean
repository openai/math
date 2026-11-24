import OAI.Computability.VPVNP.StructuredStackSafe
import OAI.Computability.VPVNP.EvaluatorRadixSpace

/-! # Time and space contracts for evaluator routines

A caller may reserve a continuation after a subroutine's clock bound. Every
branch either halts inside the subroutine or returns with an encoded output
and the reserved clock. The space predicate holds at every active instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorRoutineSafety

open RAMTape

variable {K Q R S T U : Type*} [DecidableEq K]

/-- A routine contract that maintains the stack safety predicate at active instructions and
preserves the caller's reserved fuel upon a normal return. -/
def Bounded (r : Routine K Q) (safe : Stacks K → Prop)
    (pre : S → Stacks K) (post : T → Stacks K) (B : ℕ) : Prop :=
  ∀ (extra fuel : ℕ), extra+B ≤ fuel → ∀ (x : S) (cont : ℕ → Stacks K → Prop),
    (∀ y k, extra ≤ k → cont k (post y)) → r.Safe safe cont fuel (pre x)

variable {r : Routine K Q} {r' : Routine K R} {safe : Stacks K → Prop}
  {pre : S → Stacks K} {mid : T → Stacks K} {post : U → Stacks K} {B B' : ℕ}

theorem Bounded.mono (h : Bounded r safe pre mid B) (hB : B ≤ B') :
    Bounded r safe pre mid B' :=
  fun extra fuel hf => h extra fuel ((Nat.add_le_add_left hB _).trans hf)

theorem Bounded.followedBy (ha : Bounded r safe pre mid B) (hb : Bounded r' safe mid post B') :
    Bounded (r.followedBy r') safe pre post (B+B') := by
  intro extra fuel hf x c hc
  rw [Routine.safe_followedBy]
  apply ha (extra+B') fuel (by omega)
  intro y left hl
  exact hb extra left hl y c hc

private theorem safe_of_run {r : Routine K Q} {n : ℕ} {q : Option Q} {s out : Stacks K}
    (h : StackRuns r.standalone n q s none out) (fuel : ℕ) (cont : ℕ → Stacks K → Prop)
    (hcont : cont fuel out) (prefixSafe : ∀ a (v : Q) u,
      StackRuns r.standalone a q s (some v) u → safe u) :
    r.SafeFrom safe cont (fuel+n) q s := by
  generalize hv : (none : Option Q) = target at h
  induction h with
  | nil =>
    rw [← hv]
    simpa using hcont
  | @cons q₀ s₀ q₁ s₁ q₂ s₂ n hs tail ih =>
    have later := ih hcont (fun a v u hrun => prefixSafe (a+1) v u (.cons hs hrun)) hv
    cases q₀ with
    | none => cases hs <;> contradiction
    | some q =>
      have now := prefixSafe 0 q s₀ (.nil ..)
      cases hs with
      | push h | pop h | goto h =>
        change r.code q = _ at h
        simp only [Routine.SafeFrom, h]
        exact ⟨now, later⟩

/-- A deterministic prefix satisfies the all-branch contract when every
intermediate active state satisfies the storage invariant. -/
theorem Bounded.of_runs {g : S → T} (h : ∀ x, ∃ d ≤ B, r.Runs d (pre x) (mid (g x)))
    (hspace : ∀ x n (q : Q) s, StackRuns r.standalone n (some r.entry) (pre x) (some q) s → safe s) :
    Bounded r safe pre mid B := by
  intro extra fuel hf x cont hc
  obtain ⟨d, hd, hr⟩ := h x
  have hh := safe_of_run hr (fuel-d) cont (hc _ _ (by omega)) (hspace x)
  simpa only [Nat.sub_add_cancel (show d ≤ fuel by omega)] using hh

/-- An explicit polynomial clock on a deterministic call also bounds the
increase in the length of each stack along every prefix. -/
theorem Bounded.of_runs_with_room {g : S → T}
    (h : ∀ x, ∃ d ≤ B, r.Runs d (pre x) (mid (g x)))
    (hroom : ∀ x s, (∀ k, (s k).length ≤ (pre x k).length+B) → safe s) :
    Bounded r safe pre mid B := by
  apply Bounded.of_runs h
  intro x n q s prefixRun
  obtain ⟨d, hd, hr⟩ := h x
  have hn := EvaluatorRadixDivision.ticks_le_at_return hr (by rfl) prefixRun
  exact hroom x s fun k => (EvaluatorRadixDivision.run_length prefixRun k).trans
    (Nat.add_le_add_left (hn.trans hd) _)

end EvaluatorRoutineSafety

end VPVNP
end Computability
end OAI

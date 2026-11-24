import OAI.Computability.VPVNP.RankQueryStackCursor
import OAI.Computability.VPVNP.StructuredStackLoop
import OAI.Computability.VPVNP.StructuredStackRuns

/-! # The physical descending scan for the rank query

A successful coefficient query and cursor update leave one continuation bit.
The loop requests the next pair when this bit is true and returns the rank
already stored by the update when it is false. No loop bound or matrix
dimension is part of the finite control.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape

/-- The initial and continuing states of the rank scan carry a true flag. -/
def State.continues : State → Bool
  | .running .. => true
  | .done _ => false

/-- Invoke the coefficient-and-update routine at each true mark. Its normal
return supplies the flag read by the next iteration. -/
def scan {K : Type} (flag : K) (body : FiniteRoutine K) : FiniteRoutine K :=
  .ofRoutine (Routine.popLoop flag id Routine.ret body.body)

variable {K : Type} [DecidableEq K]

/-- A physical step preserves the encoded cursor and advances it according
to the coefficient zero test. This yields a complete finite run, with a
bound uniform over every rectangular coefficient query. -/
theorem scan_runs (flag : K) (body : FiniteRoutine K) (q : ℕ → ℕ → Bool) (Z B : ℕ)
    (ready : State → Stacks K → Prop)
    (hflag : ∀ state s, ready state s → s flag = [state.continues])
    (hstep : ∀ u z s, ready (.running u z) s → ∃ k ≤ B, ∃ s',
      body.Runs k (Function.update s flag []) s' ∧ ready (step q Z (.running u z)) s')
    (state : State) (s : Stacks K) (hs : ready state s) :
    ∃ k ≤ remaining Z state * (B+1) + 2, ∃ out,
      ready (.done (answer q Z state)) out ∧ (scan flag body).Runs k s (Function.update out flag []) := by
  induction state using (measure (remaining Z)).wf.induction generalizing s with
  | h state ih =>
    cases state with
    | done r =>
      have hr := Routine.Runs.popLoop_false_stop flag id Routine.ret body.body (hflag _ s hs) rfl
        (Routine.runs_ret (Function.update s flag []))
      exact ⟨2, by simp [remaining], s, hs, hr⟩
    | running u z =>
      have dec := remaining_decreases q Z u z
      obtain ⟨k, hk, s', hh, hready⟩ := hstep u z s hs
      obtain ⟨m, hm, out, hout, hrun⟩ := ih _ dec s' hready
      have cost : 1+k+m ≤ remaining Z (.running u z) * (B+1) + 2 := by
        have h := Nat.mul_le_mul_right (B+1) dec
        rw [Nat.succ_mul] at h
        omega
      refine ⟨1+k+m, cost, out, ?_, ?_⟩
      · rwa [answer_step] at hout
      · exact Routine.Runs.popLoop_true_continue flag id Routine.ret body.body (hflag _ s hs) rfl hh hrun

/-- With the Schur coefficients this control returns the ordinary rank over
any field, including characteristic two. -/
theorem matrix_scan_runs {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) F) (get : ℕ → ℕ → F)
    (hg : ∀ u z, get u z = ((rankPolynomial M).coeff u).coeff z)
    (flag : K) (body : FiniteRoutine K) (B : ℕ)
    (ready : State → Stacks K → Prop)
    (hflag : ∀ state s, ready state s → s flag = [state.continues])
    (hstep : ∀ u z s, ready (.running u z) s → ∃ k ≤ B, ∃ s',
      body.Runs k (Function.update s flag []) s' ∧
        ready (advance ((n+m)*n) u z (decide (get u z = 0))) s')
    (s : Stacks K) (hs : ready (.running n ((n+m)*n)) s) :
    ∃ k ≤ ((n+1)*((n+m)*n+1)) * (B+1) + 2, ∃ out, ready (.done M.rank) out ∧
      (scan flag body).Runs k s (Function.update out flag []) := by
  obtain ⟨k, hk, out, hout, hr⟩ := scan_runs flag body (fun u z => decide (get u z = 0))
    ((n+m)*n) B ready hflag hstep _ s hs
  rw [initial_answer M get hg] at hout
  refine ⟨k, ?_, out, hout, hr⟩
  simpa only [remaining, Nat.succ_mul, Nat.add_assoc] using hk

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI

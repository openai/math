import OAI.Computability.VPVNP.RankCursorLoop
import OAI.Computability.VPVNP.RoutineSpace

/-!
# Bounded stack space across the descending rank scan

The loop reuses the coefficient-and-cursor workspace at each bidegree. Its
peak stack length is the same cap certified for one iteration and the
ready banks, independently of the total number of requests.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape UniversalCountStack

variable {K : Type} [DecidableEq K]

private def dispatch (body : FiniteRoutine K) : Option Bool → Option (Unit ⊕ (Unit ⊕ body.State))
  | none => none
  | some false => some (.inr (.inl ()))
  | some true => some (.inr (.inr body.body.entry))

private theorem pop_flag (flag : K) (body : FiniteRoutine K) (s : Stacks K) (b : Bool)
    (hs : s flag = [b]) :
    StackStep (scan flag body).body.standalone (some (scan flag body).body.entry) s
      (dispatch body (some b)) (Function.update s flag []) := by
  have h : StackStep (scan flag body).body.standalone (some (scan flag body).body.entry) s
      (dispatch body (s flag).head?) (Function.update s flag (s flag).tail) :=
    StackStep.pop rfl
  simpa only [hs, List.head?_cons, List.tail_cons] using h

/-- A simultaneous time and per-stack space certificate for the entire
scan. The returned register state encodes the maximum nonzero outer degree. -/
theorem scan_boundedRun (flag : K) (body : FiniteRoutine K) (q : ℕ → ℕ → Bool) (Z B cap : ℕ)
    (ready : State → Stacks K → Prop)
    (hflag : ∀ state s, ready state s → s flag = [state.continues])
    (hsafe : ∀ state s, ready state s → ∀ k, (s k).length ≤ cap)
    (hstep : ∀ u z s, ready (.running u z) s → ∃ k ≤ B, ∃ s',
      body.BoundedRun cap k (Function.update s flag []) s' ∧ ready (step q Z (.running u z)) s')
    (state : State) (s : Stacks K) (hs : ready state s) :
    ∃ k ≤ remaining Z state * (B+1) + 2, ∃ out,
      ready (.done (answer q Z state)) out ∧ (scan flag body).BoundedRun cap k s (Function.update out flag []) := by
  induction state using (measure (remaining Z)).wf.induction generalizing s with
  | h state ih =>
    have hcap := hsafe state s hs
    have pop := pop_flag flag body s state.continues (hflag state s hs)
    cases state with
    | done r =>
      have hclear (k : K) : (Function.update s flag [] k).length ≤ cap := by
        by_cases hk : k = flag <;> simp [hk, hcap]
      refine ⟨2, by simp [remaining], s, hs, SpaceRun.cons hcap pop ?_⟩
      exact .cons hclear (.goto rfl) (.nil _ _ hclear)
    | running u z =>
      have dec := remaining_decreases q Z u z
      obtain ⟨k, hk, s', hb, hready⟩ := hstep u z s hs
      obtain ⟨m, hm, out, hout, rest⟩ := ih _ dec s' hready
      have linked := hb.linkRoutine (scan flag body).body (Sum.inr ∘ Sum.inr)
        (some (scan flag body).body.entry) (fun _ => rfl)
      refine ⟨(k+m)+1, ?_, out, ?_, SpaceRun.cons hcap pop (linked.trans rest)⟩
      · have h := Nat.mul_le_mul_right (B+1) dec
        rw [Nat.succ_mul] at h
        omega
      · rwa [answer_step] at hout

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI

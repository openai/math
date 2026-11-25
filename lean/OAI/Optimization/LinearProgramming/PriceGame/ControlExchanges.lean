import OAI.Optimization.LinearProgramming.PriceGame.ControlPrefix
import OAI.Optimization.LinearProgramming.PriceGame.Campaign

/-! An exact replay of every public campaign branch by the first-order dispatcher. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open OracleSpec

/-- The campaign is evaluated with the LCM-normalized integral flow algorithm. The
trial-count function is fixed by the program; the public input supplies only N, R, and the anchor. -/
def campaignSolver (trials : ℕ → ℕ → ℕ) : PublicSolver := fun i =>
  Computation.ofTree (Campaign.strategy i.range (trials i.goods i.range) i.anchor
    (fun experts => TrialExecution.marketSolverAtCommonWeightUnit experts))

theorem campaignSolver_height (trials : ℕ → ℕ → ℕ) (i : PublicInput) :
    (campaignSolver trials i).height ≤ trials i.goods i.range *
      TrialExecution.queryBound i.goods Moment.probes (States.Mass.depth i.goods) 0 := by
  rw [← Computation.height_toTree, campaignSolver, Computation.toTree_ofTree]
  exact Campaign.strategy_height ..

/-- Evaluation under any binary answering strategy, retaining the actual transcript
of external price requests. -/
def wirePlay {α : Type*} {N : ℕ} (reply : Transcript → Word → Bool) :
    Computation N α → Transcript → α × Transcript
  | .pure a,hist => (a,hist)
  | .ask q next,hist =>
    let w := priceQuery q.index q.prices
    let b := reply hist w
    wirePlay reply (next b) ((w,[b])::hist)

/-- A first-order interaction starting from either a fresh public input or the reply
to a saved suspension. `rounds` includes the single call that emits the final sign. -/
inductive Exchanges (solver : PublicSolver) (reply : Transcript → Word → Bool) :
    Sum PublicInput (Bool × Tape) → Transcript → Bool → Transcript → ℕ → Prop
  | done {s h b} (finished : dispatch solver s = .inl b) : Exchanges solver reply s h b h 1
  | query {s h w t b out rounds} (pending : dispatch solver s = .inr (w,t))
      (rest : Exchanges solver reply (.inr (reply h w,t)) ((w,[reply h w])::h) b out rounds) :
      Exchanges solver reply s h b out (rounds+1)

private theorem observeTape_when (solver : PublicSolver) (i : PublicInput) (bs : List Bool)
    (event : Sum PublicInput (Bool × Tape)) (he : startTape event = ⟨i,bs.reverse⟩)
    (p : Computation i.goods Bool)
    (residual : ∀ more, observe (solver i) (bs ++ more) = observe p more) :
    dispatch solver event = match observe p [] with
      | .inl (b,_) => .inl b
      | .inr q => .inr (priceQuery q.index q.prices, ⟨i,bs.reverse⟩) := by
  have hobs : observe (solver i) bs = observe p [] := by simpa using residual []
  calc
    dispatch solver event = observeTape solver ⟨i, bs.reverse⟩ := congrArg (observeTape solver) he
    _ = _ := by
      unfold observeTape
      simp only [List.reverse_reverse]
      rw [hobs]
      cases observe p [] <;> rfl

private theorem exchanges_of_residual (solver : PublicSolver) (i : PublicInput)
    (reply : Transcript → Word → Bool) (p : Computation i.goods Bool) (bs : List Bool)
    (event : Sum PublicInput (Bool × Tape)) (he : startTape event = ⟨i,bs.reverse⟩)
    (residual : ∀ more, observe (solver i) (bs ++ more) = observe p more)
    (hist : Transcript) :
    ∃ rounds ≤ p.height + 1, Exchanges solver reply event hist (wirePlay reply p hist).1
      (wirePlay reply p hist).2 rounds := by
  induction p generalizing bs event hist with
  | pure a =>
    exact ⟨1,by simp [Computation.height], .done (observeTape_when solver i bs event he _ residual)⟩
  | ask q next ih =>
    let w := priceQuery q.index q.prices
    let bit := reply hist w
    let carry : Tape := ⟨i,bs.reverse⟩
    have pending : dispatch solver event = .inr (w,carry) :=
      observeTape_when solver i bs event he _ residual
    have he' : startTape (.inr (bit,carry)) = ⟨i,(bs ++ [bit]).reverse⟩ := by
      simp [carry, startTape]
    have hr' : ∀ more, observe (solver i) ((bs ++ [bit]) ++ more) = observe (next bit) more := by
      intro more
      rw [List.append_assoc, residual]
      rfl
    obtain ⟨k,hk,hplay⟩ := ih bit (bs ++ [bit]) (.inr (bit,carry)) he' hr' ((w,[bit])::hist)
    have hheight : (next bit).height ≤ max (next false).height (next true).height := by
      cases bit <;> simp
    exact ⟨k+1, by simp only [Computation.height]; omega, .query pending hplay⟩

/-- The first-order dispatcher generates exactly the same ordered queries, receives
the same replies, and returns the same bit as the whole typed computation for every
history-dependent oracle, including inconsistent ones. -/
theorem dispatch_exact (solver : PublicSolver) (i : PublicInput) (reply : Transcript → Word → Bool)
    (past : Transcript := []) :
    ∃ rounds ≤ (solver i).height + 1, Exchanges solver reply (.inl i) past
      (wirePlay reply (solver i) past).1 (wirePlay reply (solver i) past).2 rounds :=
  exchanges_of_residual solver i reply (solver i) [] (.inl i) rfl (fun _ => rfl) past

theorem actual_campaign_dispatch (trials : ℕ → ℕ → ℕ) (i : PublicInput)
    (reply : Transcript → Word → Bool) :
    ∃ rounds ≤ trials i.goods i.range * TrialExecution.queryBound i.goods Moment.probes
        (States.Mass.depth i.goods) 0 + 1,
      Exchanges (campaignSolver trials) reply (.inl i) [] (wirePlay reply (campaignSolver trials i) []).1
        (wirePlay reply (campaignSolver trials i) []).2 rounds := by
  obtain ⟨rounds,hr,hh⟩ := dispatch_exact (campaignSolver trials) i reply
  exact ⟨rounds,hr.trans (Nat.add_le_add_right (campaignSolver_height trials i) 1), hh⟩

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Geometry.Hidden
import OAI.Optimization.LinearProgramming.Geometry.PivotQueries

/-! Composition of price queries with restartable, adaptive minor queries (Section 2). -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open PriceGame

variable {N : ℕ} {κ σ α : Type*}

/-- Replace each price query by its geometric minor-query procedure. -/
def priceToMinor (label : Query N → MinorQuery κ Bool) : Tree N → MinorQuery κ Bool
  | .result v => .done v
  | .ask q next => (label q).bind fun b => priceToMinor label (next b)

theorem priceToMinor_eval (label : Query N → MinorQuery κ Bool) (f : κ → ℚ)
    (p : Tree N) (history : List (Query N × Bool)) :
    (priceToMinor label p).eval f = p.run (fun _ q => (label q).eval f) history := by
  induction p generalizing history with
  | result v => rfl
  | ask q next ih => simpa only [priceToMinor, MinorQuery.eval_bind, Tree.run] using ih _ _

/-- A minor request which signals a restart is already included in this depth bound. -/
theorem priceToMinor_bounded (label : Query N → MinorQuery κ Bool) {n : ℕ}
    (hlabel : ∀ q, (label q).Bounded n) (p : Tree N) :
    (priceToMinor label p).Bounded (n * p.height) := by
  induction p with
  | result b => exact True.intro
  | ask q next ih =>
    change ((label q).bind _).Bounded (n * (max (next false).height (next true).height + 1))
    rw [Nat.mul_succ, Nat.add_comm (n * _) n]
    refine MinorQuery.bounded_bind _ _ (hlabel q) fun b => MinorQuery.bounded_mono (ih b) ?_
    apply Nat.mul_le_mul_left
    cases b
    · exact Nat.le_max_left ..
    · exact Nat.le_max_right ..

/-- A single globally consistent log assignment suffices for a completed, adaptive price run. -/
theorem completed_minor_run_sign {R : ℕ} (hR : 1 ≤ R) (anchor : Fin N) (p : PriceGame.Tree N)
    (correct : ∀ H : Hidden N R anchor, PriceGame.Tree.Correct H p) (label : Query N → MinorQuery κ Bool)
    {log : List (κ × ℚ)} {v flag : Bool} (run : MinorQuery.Run (priceToMinor label p) log (.inr v))
    (ext : ∃ (f : κ → ℚ) (C : Finset (Fin N → ℝ)),
      (∀ e ∈ log, f e.1 = e.2) ∧ 0 < circuitEnvelope C anchor ∧
      (∀ i, 0 < circuitEnvelope C i → circuitCost C i ∈ Set.Icc 0 (R : ℝ)) ∧
      ∀ q, ValidNearLabel C flag q ((label q).eval f)) : v = flag := by
  obtain ⟨f, C, hlog, ha, hb, hv⟩ := ext
  let d := circuitInstance C flag anchor ha hb
  have hrange : d.range = R := circuitInstance_range _ _ _ _ _ hR
  have hs : PriceGame.Tree.Correct d.rounded p := by
    have hcorrect : ∀ H : Hidden N d.range anchor, PriceGame.Tree.Correct H p := hrange.symm ▸ correct
    exact hcorrect d.rounded
  have hh : ∀ history q, d.rounded.Forced q → (fun (_ : List (Query N × Bool)) q =>
      (label q).eval f) history q = d.rounded.positive := by
    intro history q hq
    exact validNearLabel_on_instance C flag anchor ha hb q (hv q)
      (States.Rounding.forced_geometric d rfl q hq)
  rw [← run.eval_of_extends f hlog, priceToMinor_eval label f p []]
  exact PriceGame.Tree.run_eq_of_correct d.rounded p hs _ hh

/-- Specialize the shared learner restart simulator to a bounded circuit envelope for each epoch. -/
theorem priceLearner_retry_correct {W : Type*} {R : ℕ} (hR : 1 ≤ R) (anchor : Fin N)
    (p : PriceGame.Tree N) (maxQueries : ℕ) (hClock : p.height ≤ maxQueries)
    (correct : ∀ H : Hidden N R anchor, PriceGame.Tree.Correct H p)
    (serve : σ → Query N → Recovery.Reply σ) (init : σ) (flag : Bool) (restarts : ℕ)
    (C : W → Finset (Fin N → ℝ))
    (ha : ∀ w, 0 < circuitEnvelope (C w) anchor)
    (hb : ∀ w i, 0 < circuitEnvelope (C w) i → circuitCost (C w) i ∈ Set.Icc 0 (R : ℝ))
    (common : ∀ {s t} (past log : List (Recovery.Event (Query N))),
      Recovery.ServicePath serve init past s → Recovery.ServicePath serve s log t →
      Recovery.restartCount log = 0 → ∃ w, ∀ q b, (q, some b) ∈ log → ValidNearLabel (C w) flag q b)
    (cap : ∀ {s} log, Recovery.ServicePath serve init log s → Recovery.restartCount log ≤ restarts) :
    let result := Recovery.run States.Restart.step serve (maxQueries + 1) p (restarts + 1) init
    result.value = some flag ∧ result.log.length ≤ (restarts + 1) * (maxQueries + 1) := by
  apply States.Restart.recover_sign_with_clock serve init flag R restarts p maxQueries hClock correct _ cap
  intro s t past log reach path zero
  obtain ⟨w, hw⟩ := common past log reach path zero
  refine ⟨circuitInstance (C w) flag anchor (ha w) (hb w), circuitInstance_range _ _ _ _ _ hR,
    rfl, rfl, ?_⟩
  exact fun q b h => validNearLabel_on_instance _ _ _ _ _ q (hw q b h)

end Geometry
end LinearProgramming
end Optimization
end OAI

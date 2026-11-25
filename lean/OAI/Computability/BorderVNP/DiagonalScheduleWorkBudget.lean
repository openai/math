import OAI.Computability.BorderVNP.DiagonalAdmissibleRange
import OAI.Computability.BorderVNP.DiagonalEpochScales
import OAI.Computability.BorderVNP.DiagonalExternalSewResourceScale
import OAI.Computability.BorderVNP.PackedHistoryBudget
import OAI.Computability.BorderVNP.RoutingISAEvalClock

/-! # Public, local and geometric work on one admissible range of processor sizes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing PackedHistoryCircuit PackedHistoryCircuit.Normalized Packing TeamScales Filter
open VPVNP.VerifierNetwork Shortening.Adaptive
open scoped Classical

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}

/-- Combined Boolean-frame and public-profile pin budget at the actual rounded height. -/
def historyWorkAt (k b d Q : ℕ) (α τ growth A : ℝ) (n r : ℕ) : Prop :=
  let T := epochs τ n
  let cap := A * (r * (n : ℝ)^(9/10 : ℝ)) * (growth^T * TeamScales.width n α) * (logWidth r n : ℝ)^d
  ∀ (σ : Type) [Fintype σ] (W G : ℕ → Type) [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
    (step : Steps k (b*T) W G) (fs : Leaves k (Frame σ (W 0)) (b*T)) (L M U : ℕ),
    ((L+1 : ℕ) : ℝ) ≤ cap → (M : ℝ) ≤ cap → (U : ℝ) ≤ cap →
    everyLeaf (fun f : Frame σ (W 0) => f.size ≤ L) (b*T) fs →
    (∀ j (hj : j<b*T), (step j hj).size + (2*k+4) ≤ M) →
    (∀ j < b*T, Fintype.card (G j) ≤ U) →
    ((Q*(compile step (b*T) le_rfl fs).size + Fintype.card (Slot k G (b*T)) : ℕ) : ℝ) <
      r * (n : ℝ)^(92/100:ℝ)

/-- Per-cell caps after external sewing, with the pre-sewing record counts. -/
def sewnWorkAt (α τ C A : ℝ) (d n r : ℕ) : Prop :=
  ∀ pub expanded : ℕ,
    (pub : ℝ) ≤ A*C^(epochs τ n)*TeamScales.width n α →
    (expanded : ℝ) ≤ A*C^(epochs τ n)*TeamScales.width n α*(n : ℝ)^(1/10+τ/20)*(logWidth r n : ℝ)^d →
    5*TeamScales.width n α*pub ≤ TeamScales.width n (1/100) ∧ 7*expanded ≤ TeamScales.width n (1/5)

/-- The instruction count of the linked evaluator on the source number of teams. -/
def evaluatorWorkAt (a d copies : ℕ) (α τ A B : ℝ) (n r : ℕ) : Prop :=
  let R := teams α τ copies n
  ∀ N core publicSteps localSteps : ℕ,
    core ≤ 2048*(exterior (τ/5) r n+(R+1)^3+N+r+1) →
    (N:ℝ) ≤ A*RoutingISA.Evaluator.publicWork a α r n R →
    (publicSteps:ℝ) ≤ B*RoutingISA.Evaluator.publicWork a α r n R →
    (localSteps:ℝ) ≤ B*RoutingISA.Evaluator.localWork a d α (τ/5) r n R →
    core+publicSteps+localSteps ≤ ticks (τ/5) r n

/-- All three families of budgets hold for one admissible batch-size exponent,
which precedes the constants multiplying the measured costs. -/
structure WorkBudget {S : SiteSchedule e} {a extra : ℕ} (s : EpochScales S a extra)
    (d Q : ℕ) (ω : ℝ) : Prop where
  history : ∀ A : ℝ, 0 ≤ A → AdmissibleRange ω
    (historyWorkAt S.fanIn S.rounds d Q s.α s.τ (epochGrowth S extra) A)
  sewn : ∀ A : ℝ, 0 ≤ A → AdmissibleRange ω (sewnWorkAt s.α s.τ (epochGrowth S extra) A d)
  evaluator : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
    AdmissibleRange ω (evaluatorWorkAt a d (epochCopies S) s.α s.τ A B)

theorem WorkBudget.shrink {S : SiteSchedule e} {a extra : ℕ} {s : EpochScales S a extra}
    {d Q : ℕ} {u v : ℝ} (budget : WorkBudget s d Q v) (le : u ≤ v) : WorkBudget s d Q u where
  history A ha := (budget.history A ha).shrink le
  sewn A ha := (budget.sewn A ha).shrink le
  evaluator A B ha hb := (budget.evaluator A B ha hb).shrink le

theorem exists_workBudget {S : SiteSchedule e} {a extra : ℕ} (s : EpochScales S a extra)
    (ha : 1 ≤ a) (d Q : ℕ) : ∃ ω : ℝ, 0 < ω ∧ WorkBudget s d Q ω := by
  have α0 : 0 < (s.α : ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 < (s.τ : ℝ) := by exact_mod_cast s.tau_pos
  have αsmall := s.alpha_small
  have τsmall := s.tau_small
  have caps := epochGrowth_bounds S extra
  have hG : 1 ≤ (epochGrowth S extra : ℝ) := by exact_mod_cast caps.1
  have growth := s.rate (epochCopies_pos S) caps.2.1
  have hcopy : (s.τ : ℝ)*Real.logb 2 (epochCopies S) ≤ (s.α : ℝ) := by linarith
  obtain ⟨vh,hh,hist⟩ := eventually_compiled_history_92 S.rounds d Q αsmall τ0 τsmall
    S.positiveFanIn hcopy hG s.growth.le
  obtain ⟨vs,hs,sew⟩ := ExternalSew.eventually_sewn_resources αsmall τ0 τsmall
    (epochCopies_pos S) hcopy hG s.growth.le d
  obtain ⟨ve,he,exec⟩ := RoutingISA.Evaluator.eventually_eval_clock a d ha α0.le
    s.alpha_cube (by positivity : 0 < (s.τ : ℝ)/5) (by linarith : (s.τ : ℝ)/5 < 1/25)
  refine ⟨min vh (min vs ve), lt_min hh (lt_min hs he), ⟨?_,?_,?_⟩⟩
  · intro A hA
    exact (show AdmissibleRange vh _ from hist A hA).shrink (min_le_left ..)
  · intro A hA
    exact (show AdmissibleRange vs _ from sew A hA).shrink ((min_le_right ..).trans (min_le_left ..))
  · intro A B hA hB
    apply AdmissibleRange.shrink (v := ve) _ ((min_le_right ..).trans (min_le_right ..))
    filter_upwards [exec A B hA hB, eventually_many_teams α0 (s.τ:ℝ) (epochCopies_pos S) 1,
      eventually_ge_atTop 1] with n hn hR one
    intro r hr up N c pub loc hc hN hp hl
    exact hn r _ N c pub loc hr hR up (teams_le (epochCopies_pos S) one τ0.le hcopy) hc hN hp hl

end Diagonal

end BorderVNP
end Computability
end OAI

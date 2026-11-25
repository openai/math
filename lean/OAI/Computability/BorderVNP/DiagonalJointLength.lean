import OAI.Computability.BorderVNP.DiagonalJointSchedule

/-! # Simultaneous room on the actual stretched sequence of lengths

The rounded output offset is one below the terminal site depth. This
identifies each program's input cover with the preceding epoch's output.
The chart is selected only after the processor length and ground field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover Epoch Packing PackedHistoryCircuit.Normalized TeamScales
open VPVNP MvPolynomial Branch

universe u v

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}
variable {S : SiteSchedule e} {a extra : ℕ} {s : EpochScales S a extra} {E d Q A B j : ℕ}

/-- The parse network fits at the largest admitted candidate size. The
geometric estimates use the exact rounded initial and terminal covers. -/
structure LengthBudget (b : JointSchedule.{u} s E d Q A B j) (cut n : ℕ) : Prop where
  replication : (n + stretch b.σ n + 2)^24 ≤ stretch b.ρ n
  parse : ((180000000*(n*stretch b.ρ n)*(Nat.clog 2 (2*n*stretch b.ρ n)+3)^3 : ℕ):ℝ) ≤
    volume s.τ (stretch b.ρ n) n
  teams : 3 ≤ b.physical.teamsPred n+1 ∧ (b.physical.teamsPred n+1:ℕ) ≤ (n:ℝ)^(2*(s.α:ℝ))
  cover : let r := stretch b.ρ n
    let start := CoverScale.initialDepth (Cube D) r n
    let finish := start-S.drop*epochs s.τ n
    S.floor+1 ≤ finish ∧ finish+S.drop*epochs s.τ n = start ∧
    (r:ℝ)*(n:ℝ)^(9/10:ℝ)/CoverScale.factor (Cube D) < CoverScale.sites (Cube D) start ∧
    (CoverScale.sites (Cube D) start:ℝ) ≤ (r:ℝ)*(n:ℝ)^(9/10:ℝ) ∧
    (r:ℝ)*(n:ℝ)^(9/10-(s.α:ℝ)/10)/CoverScale.factor (Cube D) < CoverScale.sites (Cube D) finish
  offsets : let start := CoverScale.initialDepth (Cube D) (stretch b.ρ n) n
    ∀ t < epochs s.τ n, ∃ low ≥ S.floor,
      low+1 = start-S.drop*(t+1) ∧ S.high low = start-S.drop*t
  levels : let start := CoverScale.initialDepth (Cube D) (stretch b.ρ n) n
    let word := fun i => (S.source.pattern i).word
    (∀ t i, Shortening.PublicCapacity.seedDepth word S.last start t i ≤ start+1) ∧
    ∀ t < epochs s.τ n, ∀ i, ∃ z : ℕ, 1 ≤ z ∧
      z+2*word i = Shortening.PublicCapacity.seedDepth word S.last start t i ∧
      cut ≤ z+2*word i+2*word i ∧
      z+2*word i+2*word i =
        Shortening.Adaptive.Levels.level word (Shortening.PublicCapacity.terminalDepth word S.last start t) S.last i.val+1
  localCall : PacketBudgetAt A B j n (stretch b.ρ n)
  logs : (logWidth (stretch b.ρ n) n:ℝ)^d ≤ (n:ℝ)^((s.τ:ℝ)/2000)

theorem JointSchedule.eventually_lengths (b : JointSchedule.{u} s E d Q A B j) (cut : ℕ) :
    ∀ᶠ n : ℕ in atTop, LengthBudget b cut n := by
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have cov := s.rate (epochCoverLoss_pos S) (epochGrowth_bounds S extra).2.2.1
  have he : (s.τ:ℝ)*Real.logb 2 ((CoverScale.factor (Cube D):ℝ)^S.drop) ≤ (s.α:ℝ)/10 := by
    simpa only [epochCoverLoss,Nat.cast_pow] using cov
  have small : (s.α:ℝ)/10 < 9/10 := by linarith [s.alpha_small]
  have cover := CoverScale.eventually_depths (Cube D) S.drop S.floor τ0.le he small
  have seeds := Shortening.PublicCapacity.eventually_schedule_levels (fun i => (S.source.pattern i).word) S.last
    (Cube D) cut τ0.le he small
  filter_upwards [ParseBatchVerifier.eventually_replication b.sigma_pos b.sigma_rho,
    ParseBatchVerifier.eventually_parse_volume (b.sigma_pos.trans b.sigma_rho) b.parse_gap,
    eventually_many_teams α0 (s.τ:ℝ) (epochCopies_pos S) 3,cover,seeds,
    b.machine.packet.stretched b.rho_omega.le,b.machine.log.stretched b.rho_omega.le,
    eventually_ge_atTop 1] with n rep parse many sites ranges packet logs hn
  let r := stretch b.ρ n
  let start := CoverScale.initialDepth (Cube D) r n
  have hc := sites r (stretch_one ..)
  refine ⟨rep,parse,?_,hc,?_,ranges r (stretch_one ..),packet,logs⟩
  · rw [(b.sizes hn).1]
    exact ⟨many,teams_le (epochCopies_pos S) hn τ0.le s.copy_rate⟩
  · change ∀ t < epochs s.τ n, ∃ low ≥ S.floor,
      low+1 = start-S.drop*(t+1) ∧ S.high low = start-S.drop*t
    intro t ht
    let T := epochs s.τ n
    have cap : S.drop*T ≤ start := by
      have q : start-S.drop*T+S.drop*T=start := hc.2.1
      omega
    have ht' : t+1 ≤ T := ht
    have used := Nat.mul_le_mul_left S.drop ht'
    have floor : S.floor+1 ≤ start-S.drop*T := hc.1
    have hi : S.drop*(t+1) = S.drop*t+S.drop := Nat.mul_succ ..
    have hu : S.drop*t+S.drop ≤ start := hi ▸ used.trans cap
    have back : start-S.drop*(t+1)-1+1 = start-S.drop*(t+1) := by omega
    refine ⟨start-S.drop*(t+1)-1,by omega,by omega,?_⟩
    change (start-S.drop*(t+1)-1+1)+S.drop = start-S.drop*t
    rw [back,hi]
    omega

/-- Every rounded execution in this common range has its genuine calibrated
enriched state program, leaves and terminal bounds at the required absolute level. -/
theorem LengthBudget.epochs {b : JointSchedule.{u} s E d Q A B j} {cut n : ℕ}
    (h : LengthBudget b cut n)
    (run : ∀ z ≥ S.floor, S.FitsLevels z ∧ S.HasLeaves z ∧ S.RunsEnriched.{v} z) :
    let start := CoverScale.initialDepth (Cube D) (stretch b.ρ n) n
    ∀ t < TeamScales.epochs s.τ n, ∃ z, S.high z = start-S.drop*t ∧
      z+1 = start-S.drop*(t+1) ∧ S.FitsLevels z ∧ S.HasLeaves z ∧ S.RunsEnriched.{v} z := by
  intro start t ht
  obtain ⟨z,good,finish,initial⟩ := h.offsets t ht
  exact ⟨z,initial,finish,run z good⟩

end Diagonal

end BorderVNP
end Computability
end OAI

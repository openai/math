import OAI.Computability.BorderVNP.DiagonalScheduleGeometry
import OAI.Computability.BorderVNP.DiagonalScheduleProgramBudget
import OAI.Computability.BorderVNP.DiagonalScheduleMachineBudget
import OAI.Computability.BorderVNP.DiagonalScheduleWorkBudget
import OAI.Computability.BorderVNP.DiagonalScheduledSizes
import OAI.Computability.BorderVNP.ParseBatchStretchScale

/-! # A simultaneous physical schedule for the border diagonal

The shortening and cube fix the rational scales. The common processor
exponent is reduced to meet all fixed-program bounds. The replication
and candidate-circuit exponents are chosen strictly inside that range.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Packing PackedHistoryCircuit.Normalized Cover Epoch TeamScales

universe u v

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}

theorem EpochScales.copy_rate {S : SiteSchedule e} {a extra : ℕ} (s : EpochScales S a extra) :
    (s.τ : ℝ)*Real.logb 2 (epochCopies S) ≤ (s.α : ℝ) := by
  have h := s.rate (epochCopies_pos S) (epochGrowth_bounds S extra).2.1
  have pos : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  linarith

/-- Exponents and uniform runtime estimates for the same normalized epoch
and fixed machine-size choices. The fourth and fifth integer parameters
bound the packet translator, independent of the later field chart. -/
structure JointSchedule {S : SiteSchedule e} {a extra : ℕ} (s : EpochScales S a extra)
    (E d Q A B j : ℕ) where
  /-- Largest admitted batch exponent. -/
  ω : ℝ
  /-- Exponent of the actual batch size. -/
  ρ : ℝ
  /-- Exponent of the candidate circuit size. -/
  σ : ℝ
  sigma_pos : 0 < σ
  sigma_rho : σ < ρ
  rho_omega : ρ < ω
  parse_gap : 3*ρ < (s.τ:ℝ)/20
  publicWork : WorkBudget s d Q ω
  geometry : GeometryBudget E d (epochCopies S) s.α s.τ ω
  program : ProgramBudget s.α s.τ E d ω
  machine : MachineBudget.{u} s.α s.τ E d A B j ω

/-- Choose the processor exponent after the fixed machine and history bounds
are known. Any additional fixed-program cutoff can be included in the same
choice. Neither stretched-exponential parameter has yet been selected. -/
theorem exists_jointSchedule {S : SiteSchedule e} {a extra : ℕ} (s : EpochScales S a extra)
    (ha : 1 ≤ a) (E d Q A B j : ℕ) {limit : ℝ} (hlimit : 0 < limit) :
    ∃ b : JointSchedule.{u} s E d Q A B j, b.ω ≤ limit := by
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  obtain ⟨wm,hm,machine⟩ := exists_machineBudget.{u} α0 s.alpha_small τ0 s.tau_small E d A B j
  obtain ⟨wg,hg,geometry⟩ := exists_geometryBudget α0 s.alpha_small τ0 s.tau_small E d (epochCopies S)
  obtain ⟨wp,hp,work⟩ := exists_workBudget s ha d Q
  obtain ⟨wt,ht,program⟩ := exists_programBudget α0 s.alpha_small τ0 s.tau_small E d
  let ω := min limit (min wt (min wp (min wg wm)))
  have hω : 0 < ω := lt_min hlimit (lt_min ht (lt_min hp (lt_min hg hm)))
  let ρ := min ω ((s.τ:ℝ)/60)/2
  have hρ : 0 < ρ := by dsimp [ρ]; exact div_pos (lt_min hω (by positivity)) (by norm_num)
  have hρw : ρ < ω := by
    have h := min_le_left ω ((s.τ:ℝ)/60)
    dsimp [ρ]; linarith
  have gap : 3*ρ < (s.τ:ℝ)/20 := by
    have h := min_le_right ω ((s.τ:ℝ)/60)
    dsimp [ρ]; linarith
  have hus : ω ≤ min wt (min wp (min wg wm)) := min_le_right ..
  have hu := hus.trans (min_le_right ..)
  have hgm := hu.trans (min_le_right ..)
  exact ⟨⟨ω,ρ,ρ/2,by positivity,by linarith,hρw,gap,
    work.shrink (hu.trans (min_le_left ..)), geometry.shrink (hgm.trans (min_le_left ..)),
    program.shrink (hus.trans (min_le_left ..)),machine.shrink (hgm.trans (min_le_right ..))⟩,min_le_left ..⟩

variable {S : SiteSchedule e} {a extra : ℕ} {s : EpochScales S a extra} {E d Q A B j : ℕ}

/-- Use the actual evaluator's 64-register sorter edge type. The subtotal
and occurrence words share the chosen RAM word capacity. -/
noncomputable def JointSchedule.physical (b : JointSchedule.{u} s E d Q A B j) : StretchSchedule :=
  physicalSchedule b.sigma_pos b.sigma_rho (epochCopies S) (epochCopies_pos S)
    (by exact_mod_cast s.tau_pos.le) s.copy_rate (by linarith [s.alpha_small]) 64 (E+1) (E+1) (E+1)

/-- The source multiplicity and all machine widths agree on every positive input. -/
theorem JointSchedule.sizes (b : JointSchedule.{u} s E d Q A B j) {n : ℕ} (hn : 1 ≤ n) :
    let R := teams s.α s.τ (epochCopies S) n
    let w := logWidth (stretch b.ρ n) n^(E+1)
    b.physical.teamsPred n+1 = R ∧ b.physical.link n = link ((s.τ:ℝ)/5) R n ∧
    b.physical.word n = w ∧ b.physical.tally n = w ∧ b.physical.multBits n = w := by
  refine ⟨?_,rfl,rfl,rfl,rfl⟩
  apply physicalSchedule_teams
  · exact_mod_cast s.alpha_pos.le
  · exact hn

/-- Calibration precedes all hardware and length choices. The returned
normalized epoch runs on enriched public states, including complete-pin programs. -/
theorem exists_calibrated_scales (K : Type*) [Field K] (e : PaidIdentity F D m)
    (hm : 0 < m) (minimum extra : ℕ) :
    ∃ cube : FixedCube K, minimum ≤ cube.h*cube.b ∧
      ∃ S : SiteSchedule e, (∀ t ≥ S.floor, S.FitsLevels t ∧ S.HasLeaves t ∧ S.RunsEnriched.{v} t) ∧
        Nonempty (EpochScales S (cube.pred+1) extra) := by
  obtain ⟨cube,hc⟩ := exists_fixedCube K minimum
  obtain ⟨S,run⟩ := exists_enriched_executions.{v} e hm
  exact ⟨cube,hc,S,run,exists_epochScales S (cube.pred+1) extra (by omega)⟩

end Diagonal

end BorderVNP
end Computability
end OAI

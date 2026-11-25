import OAI.Computability.BorderVNP.DiagonalJointLength
import OAI.Computability.BorderVNP.DiagonalSchedulePrivateBudget

/-! # The fixed cube, calibrated epochs and physical program on one stretch schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing PackedHistoryCircuit.Normalized TeamScales VPVNP.BurstRAM

universe u v

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {e : PaidIdentity F D m}

/-- Fix the prime-field cube, calibrated shortening and rational exponents.
The later integer overheads may depend on that calibration. All processor and
circuit exponents are fixed before any length, finite branch field or program
input is supplied. The selected schedule uses word power at least two. -/
theorem exists_physical_schedule (K : Type*) [Field K] (e : PaidIdentity F D m)
    (hm : 0 < m) (minimum : ℕ) :
    ∃ cube : FixedCube K, minimum ≤ cube.h*cube.b ∧
    ∃ S : SiteSchedule e, (∀ z ≥ S.floor, S.FitsLevels z ∧ S.HasLeaves z ∧ S.RunsEnriched.{v} z) ∧
    ∀ extra : ℕ, ∃ s : EpochScales S (cube.pred+1) extra,
    ∀ E d Q A T B j H R k : ℕ, ∀ limit : ℝ, 0 < limit →
    ∃ b : JointSchedule.{u} s (E+1) d Q A B j, b.ω ≤ limit ∧
      AdmissibleRange b.ω (PrivateCellBudgetAt A T B j H R k) ∧
      ∀ cut : ℕ, ∀ᶠ n : ℕ in atTop,
        LengthBudget b cut n ∧ PrivateCellBudgetAt A T B j H R k n (stretch b.ρ n) := by
  obtain ⟨cube,hc⟩ := exists_fixedCube K minimum
  obtain ⟨S,run⟩ := exists_enriched_executions.{v} e hm
  refine ⟨cube,hc,S,run,?_⟩
  intro extra
  obtain ⟨s⟩ := exists_epochScales S (cube.pred+1) extra (by omega)
  refine ⟨s,?_⟩
  intro E d Q A T B j H R k limit hlimit
  obtain ⟨v,hv,_,cell⟩ := exists_machineBudget_with_private.{u}
    (by exact_mod_cast s.alpha_pos) s.alpha_small (by exact_mod_cast s.tau_pos) s.tau_small
    (E+1) d A T B j H R k
  obtain ⟨b,hb⟩ := exists_jointSchedule.{u} s (by omega) (E+1) d Q A B j (lt_min hlimit hv)
  have fit := cell.shrink (hb.trans (min_le_right ..))
  exact ⟨b,hb.trans (min_le_left ..),fit,fun cut => (b.eventually_lengths cut).and (fit.stretched b.rho_omega.le)⟩

variable {S : SiteSchedule e} {a extra : ℕ} {s : EpochScales S a extra} {E d Q A B j : ℕ}

/-- The actual frame, record caps, program's complete routing clock, serialized
geometry, sorter lanes and validator fit at one length. The program and costs
precede the common threshold. The tested descriptor, private input and the
counts of its execution may vary afterward. -/
theorem JointSchedule.eventually_runs (b : JointSchedule.{u} s E d Q A B j) (cut c : ℕ)
    (P₁ P₂ : ℝ) (h₁ : 0 ≤ P₁) (h₂ : 0 ≤ P₂)
    {pc μ g : ℕ} {Qstate Γ : Type} [Fintype Qstate]
    (P : TeamOpcode.Program pc 64 32 8) (lib : Fin 8 → TeamSite.Macro Qstate Γ μ g) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let w := b.physical.word n
      LengthBudget b cut n ∧
      historyWorkAt S.fanIn S.rounds d Q s.α s.τ (epochGrowth S extra) P₁ n r ∧
      sewnWorkAt s.α s.τ (epochGrowth S extra) P₁ d n r ∧
      evaluatorWorkAt a d (epochCopies S) s.α s.τ P₁ P₂ n r ∧
      jointGeometryAt P lib E d (epochCopies S) s.α s.τ P₁ P₂ n r ∧
      c*TeamContraction.Wires.innerWidth r 64 w
        (TeamContraction.Wires.sortExponent (block ((s.τ:ℝ)/5) n)) (w+1) ≤ n :=
  (b.eventually_lengths cut).and (((b.publicWork.history P₁ h₁).stretched b.rho_omega.le).and
    (((b.publicWork.sewn P₁ h₁).stretched b.rho_omega.le).and
      (((b.publicWork.evaluator P₁ P₂ h₁ h₂).stretched b.rho_omega.le).and
        (((b.geometry P₁ P₂ h₁ h₂ P lib).stretched b.rho_omega.le).and
          ((b.machine.ports c).stretched b.rho_omega.le)))))

end Diagonal

end BorderVNP
end Computability
end OAI

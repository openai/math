import OAI.Computability.BorderVNP.DiagonalJointLength
import OAI.Computability.BorderVNP.DiagonalExternalSewScale
import OAI.Computability.BorderVNP.CubeGroupChargeRoom

/-! # Simultaneous cell, cube-group and exterior budgets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing PackedHistoryCircuit.Normalized TeamScales Packing Epoch
open VPVNP BurstRAM TeamContraction

universe u

variable {D m : ℕ} [NeZero D] {F : Type*} [Field F] {G : PaidIdentity F D m}
variable {S : SiteSchedule G} {a extra : ℕ} {s : EpochScales S a extra} {E d Q A B j : ℕ}

/-- The same rational parameters meet the slack and traffic conditions used
for native label selection and cube-group enumeration. -/
theorem EpochScales.label_slack (s : EpochScales S a extra) :
    (s.τ:ℝ)/5 < (s.α:ℝ)/3 ∧
    24*(s.α:ℝ)*a+1/4 < 1-(s.τ:ℝ)/5 ∧ 8*(s.α:ℝ)*a < 1-(s.τ:ℝ)/5 := by
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have bounds := s.alpha_cube
  have hτ := s.tau_small
  have hs := s.alpha_small
  refine ⟨?_,?_,?_⟩ <;> nlinarith only [α0,bounds,hτ,hs]

/-- Word blocks at the exact input-cover volume fit the literal and exterior
links. Packet padding and loads fit for the actual cube block size. -/
theorem JointSchedule.eventually_placement {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s E d Q A B j) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let V := CoverScale.sites (Cube D) (CoverScale.initialDepth (Cube D) r n)
      let ξ := (s.τ:ℝ)/5
      let l := Cube.alphabet s.α n
      let X := exterior ξ r n*R
      (∀ slots : ℕ, 0 < slots → slots ≤ r*n → let g := Packing.blockWidth slots V
        0 < g ∧ slots ≤ V*g ∧ g ≤ literal s.α n ∧ g ≤ b.physical.link n) ∧
      ((cube.pred+1:ℕ):ℝ)/l ≤ 1/10^6 ∧ 1024*(10*(M+1)+4)*R ≤ l ∧
      Cube.Physical.blocksFor X (cube.h*cube.b) (l^(cube.pred+1)) *
        (cube.h*cube.b)*(l^(cube.pred+1))^2 ≤ 5*X ∧
      ∀ z : ℕ, z ≤ 3*R*r*literal s.α n → 4096*z ≤ X := by
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have cap := ExternalSew.eventually_block_fields (Cube D) α0 s.alpha_small τ0.le s.tau_small
    (epochCopies_pos S) s.copy_rate
  have cub := Cube.Physical.eventually_group_charge_room α0 s.label_slack.1 (cube.pred+1)
    (cube.h*cube.b) M cube.block_pos s.label_slack.2.2
  filter_upwards [cap,cub,b.eventually_lengths 0,eventually_ge_atTop 1] with n hb hc fits hn
  let r := stretch b.ρ n
  have hr := stretch_one b.ρ n
  have gr := hc r _ hr (by have := fits.teams.1; omega) fits.teams.2
  exact ⟨hb r hr,gr⟩

/-- A trusted timed or field-valued processor has the correct sorter geometry
and complete literal stream, while the final nonlocal width fits the budget.
All three conclusions refer to the same processor and team parameters. -/
theorem JointSchedule.eventually_program (b : JointSchedule.{u} s E d Q A B j)
    {pc μ g : ℕ} {Qstate Γ : Type} [Fintype Qstate]
    (P : TeamOpcode.Program pc 64 32 8) (lib : Fin 8 → TeamSite.Macro Qstate Γ μ g)
    (physical : UniversalMachine.Program) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      FieldProcessor.Scale physical pc 64 32 s.α ((s.τ:ℝ)/5) r n (b.physical.teamsPred n)
        (b.physical.word n) (Wires.sortExponent (block ((s.τ:ℝ)/5) n)) ∧
      programStreamAt physical E d s.α C n r ∧
      nonlocalWidthAt s.τ d C S.error ε n r := by
  filter_upwards [(b.program.table P lib physical).stretched b.rho_omega.le,
    (b.program.stream C hC physical).stretched b.rho_omega.le,
    (b.program.nonlocalWidth C S.error ε hC S.error_pos.le hε).stretched b.rho_omega.le]
    with n geom stream nonlocalWidth
  exact ⟨geom _,stream,nonlocalWidth⟩

end Diagonal

end BorderVNP
end Computability
end OAI

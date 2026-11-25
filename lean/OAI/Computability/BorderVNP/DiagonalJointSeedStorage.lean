import OAI.Computability.BorderVNP.PackedSeedParseCaps
import OAI.Computability.BorderVNP.DiagonalJointLength
import OAI.Computability.BorderVNP.PackedBankSelectedWordRoom

/-! # Original tape and per-cell budgets on the already selected processor sequence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover BorderVNP.Epoch Packing DeckGrid Filter TeamScales ExternalSew
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube
open private record_pos from OAI.Computability.BorderVNP.PackedSelectedRecordRanges

universe u
variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The numerical charges of the complete initialized original bank, throughout
the propagated public/expanded history and its final description deliveries. -/
def SeedStorage (q n r d copies T fan factor header : ℕ) (α : ℝ) : Prop :=
  let degree := Fintype.card (Direction q)
  let H := seedChannelWidth n r q d
  let cap := seedBoxCapacity n r q d degree
  let dB := seedDescriptionWidth n r q d (header*logWidth r n) (BottomGridBank.bodyBudget cap)
  let mass := factor^T*baseMass degree cap H copies dB
  5*copies*(factor^T*seedPublicBase degree) ≤ TeamScales.width n (1/100) ∧
    7*mass ≤ TeamScales.width n (1/5) ∧ 7*mass < 2^(60*logWidth r n) ∧
    dB ≤ literal α n/2 ∧ fan^T*GridHosts.tileCount q d*dB ≤ copies*fan^T*r*(literal α n/2)

/-- This works on the common chosen stretched sequence itself. The threshold
does not request a further restriction on the stretch exponent. -/
theorem JointSchedule.eventually_seedStorage (b : JointSchedule.{u} s E deg Q A B j) (factor header : ℕ)
    (positive : 1 ≤ factor) (rate : (s.τ:ℝ)*Real.logb 2 factor ≤ 2*(s.α:ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      SeedStorage (Fintype.card (Cube D)) n r d (TeamScales.width n s.α) (epochs s.τ n) (S.fanIn^S.rounds) factor header s.α := by
  let q := Fintype.card (Cube D)
  let _ : NeZero q := ⟨Fintype.card_pos.ne'⟩
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have caps := eventually_seed_actual_caps_of_parse α0 s.alpha_small τ0 s.tau_small positive rate
    q (Fintype.card (Direction q)) header
  filter_upwards [b.eventually_lengths 0,caps,eventually_ge_atTop 1] with n h room hn
  intro r d
  have hr : 1 ≤ r := stretch_one ..
  let start := CoverScale.initialDepth (Cube D) r n
  have hstart : 1 ≤ start := Nat.succ_pos _
  have hd : d+1=start := by dsimp only [d,start] at *; omega
  have tile : GridHosts.tileCount q d = CoverScale.sites (Cube D) start := by
    rw [←hd]
    simp only [q,GridHosts.tileCount,CoverScale.sites,Fintype.card_fun,Fintype.card_fin]
  have fac : CoverScale.factor (Fin q) = CoverScale.factor (Cube D) := by
    simp only [q,CoverScale.factor,Fintype.card_fun,Fintype.card_fin]
  have raw := room r d hr
  obtain ⟨sparse,expanded,individual,total⟩ := raw (tile ▸ h.cover.2.2.2.1)
    (by rw [fac,tile]; exact h.cover.2.2.1) h.parse
  have small : TeamScales.width n (1/5) ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1 ≤ (n:ℝ)) (by norm_num : (1/5:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have bits := Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r hr)
  refine ⟨sparse,expanded,expanded.trans_lt (small.trans_lt (bits.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))),
    individual,total _⟩

/-- The geometric record propagation in every genuine terminal of the chosen plan. -/
theorem JointSchedule.eventually_geometricSeedStorage (b : JointSchedule.{u} s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      SeedStorage (Fintype.card (Cube D)) n r d (TeamScales.width n s.α) (epochs s.τ n) (S.fanIn^S.rounds) S.recordFactor header s.α := by
  have pos := record_pos S
  have h : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  exact b.eventually_seedStorage _ _ pos ((s.rate pos (epochGrowth_bounds S extra).2.2.2.1).trans (by linarith))

/-- The genuine propagated stored-program mass fits the physical selector
and final cell addressing width on that very same processor sequence. -/
theorem JointSchedule.eventually_programSeedStorage {K : Type} [Field K]
    {e : PaidIdentity K D m} {S : SiteSchedule e} {s : EpochScales S a extra}
    (b : JointSchedule.{u} s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      SeedStorage (Fintype.card (Cube D)) n r d (TeamScales.width n s.α) (epochs s.τ n) (S.fanIn^S.rounds) S.publicProgramFactor header s.α := by
  have pos : 0 < S.publicProgramFactor := by
    unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor
    positivity
  have alpha : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  exact b.eventually_seedStorage _ _ pos ((calibrated_program_rate S s).trans (by linarith))

end Diagonal

end BorderVNP
end Computability
end OAI

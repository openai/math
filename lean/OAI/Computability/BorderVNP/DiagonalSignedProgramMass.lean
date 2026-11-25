import OAI.Computability.BorderVNP.DiagonalJointSeedStorage
import OAI.Computability.BorderVNP.PackedHistorySeedWord

/-! # The scaled immutable program mass in the chosen diagonal schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover CoverScale TeamScales Filter Diagonal.ExternalSew

/-- Any fixed charge per physical node is absorbed by the strict exponent gap of the original parse bound. -/
theorem eventually_scaled_seed_mass {α τ : ℝ} (ha : 0<α) (small : α<1/1000)
    (ht : 0<τ) (tiny : τ<α/100) {C : ℕ} (factorPos : 1≤C) (growth : τ*Real.logb 2 C ≤ 2*α)
    (q degree headerFactor c : ℕ) [NeZero q] :
    ∀ᶠ n : ℕ in atTop, ∀ r depth : ℕ, 1≤r →
      let V := GridHosts.tileCount q depth
      (V:ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) → (r:ℝ)*(n:ℝ)^(9/10:ℝ)/factor (Fin q)<V →
      (batchVolume n r:ℝ) ≤ volume τ r n →
      let H := seedChannelWidth n r q depth
      let cap := seedBoxCapacity n r q depth degree
      let dB := seedDescriptionWidth n r q depth (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
      let b := width n α
      let T := epochs τ n
      let M := C^T*baseMass degree cap H b dB
      c*M ≤ width n (1/5) := by
  let β := 1/10+τ/5
  let A := seedPublicBase degree+12+810489*(11+2*degree)+(2*degree+1)+1
  have sizes := eventually_seed_stored_of_parse ht (by linarith) q degree headerFactor
  have mass := eventually_le_rounded_width (show 2*α+α+β < 1/5 by dsimp [β]; linarith)
    (by norm_num) (by norm_num : (0:ℝ)<1) ((c:ℝ)*A)
  filter_upwards [sizes,mass,eventually_ge_atTop 1] with n nsize nm hn
  intro r d hr V hv large parse H cap dB b T M
  have hn' : 1≤(n:ℝ) := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn'
  have hC : 1≤(C:ℝ) := by exact_mod_cast factorPos
  have hfactor : ((C^T:ℕ):ℝ) ≤ (n:ℝ)^(2*α) := by exact_mod_cast epoch_growth_le hC hn ht.le growth
  have hb : (b:ℝ)≤(n:ℝ)^α := Nat.floor_le (by positivity)
  have one : 0<b := Nat.le_floor (by simpa using Real.one_le_rpow hn' ha.le)
  have store : 1+H+dB ≤ (n:ℝ)^β := (nsize r d hr hv large parse).2
  have raw := (baseMass_scale n r q d degree b dB one).2
  have data : (baseMass degree cap H b dB:ℝ) ≤ A*b*(1+H+dB) := by exact_mod_cast raw
  have factor' : (C:ℝ)^T ≤ (n:ℝ)^(2*α) := by exact_mod_cast hfactor
  apply (Nat.cast_le (α:=ℝ)).mp
  dsimp only [M]
  push_cast
  calc
    _ ≤ (c:ℝ)*((n:ℝ)^(2*α)*((A:ℝ)*(n:ℝ)^α*(n:ℝ)^β)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact mul_le_mul factor' (data.trans (mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) store (by positivity) (by positivity))) (by positivity) (by positivity)
    _ = ((c:ℝ)*A:ℝ)*(n:ℝ)^(2*α+α+β) := by rw [Real.rpow_add hn0 (2*α+α) β,Real.rpow_add hn0 (2*α) α]; ring
    _ ≤ _ := by simpa only [one_mul] using nm

end Packing.DeckGrid

namespace Diagonal

open Crossing Cover BorderVNP.Epoch Packing DeckGrid Filter TeamScales ExternalSew
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube
open PackedHistoryCircuit.Normalized.SelectedSchedule

universe u
variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- One common length threshold pays all staged rows and their guards at the actual
cover level, for the prescribed replication count and true privately stored seed. -/
theorem JointSchedule.eventually_signed_program_mass (b : JointSchedule.{u} s E deg Q A B j) (header c : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      c*(S.publicProgramFactor^epochs s.τ n*initialMass (D:=D) n r d (TeamScales.width n s.α) header) ≤
        TeamScales.width n (1/5) := by
  let q := Fintype.card (Cube D)
  let _ : NeZero q := ⟨Fintype.card_pos.ne'⟩
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have τ0 : 0 < (s.τ:ℝ) := by exact_mod_cast s.tau_pos
  have positive : 0 < S.publicProgramFactor := by
    unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor Epoch.Round.epochRecordFactor
    positivity
  have rate : (s.τ:ℝ)*Real.logb 2 S.publicProgramFactor ≤ 2*(s.α:ℝ) := (calibrated_program_rate S s).trans (by linarith)
  have caps := eventually_scaled_seed_mass α0 s.alpha_small τ0 s.tau_small positive rate q (Fintype.card (Direction q)) header c
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
  exact raw (tile ▸ h.cover.2.2.2.1)
    (by rw [fac,tile]; exact h.cover.2.2.1) h.parse

end Diagonal

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.PackedSelectedSeedRanges
import OAI.Computability.BorderVNP.PackedSeedBaseCaps

/-! # Word fits for the actual grouped bottom grid and its full birth payload -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch Packing Shortening PublicCapacity Diagonal Diagonal.ExternalSew
open TeamScales Filter EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

local notation "axes" => Fintype.card (Cube D)
local notation "degree" => Fintype.card (DeckGrid.Direction axes)

/-- The actual per-tile initial record budget, including the one-copy
factor table, repeated evaluation slab and every private delivery. -/
noncomputable def initialMass (n r d copies headerFactor : ℕ) : ℕ :=
  let cap := DeckGrid.seedBoxCapacity n r axes d degree
  let dB := DeckGrid.seedDescriptionWidth n r axes d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
  DeckGrid.baseMass degree cap (DeckGrid.seedChannelWidth n r axes d) copies dB

set_option maxHeartbeats 800000 in
/-- The chosen one-copy descriptor, repeated width and all tile addresses fit
before the verifier's private witness is supplied. -/
theorem eventually_initial_words {a x : ℕ} (scales : EpochScales S a x) (headerFactor : ℕ) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      let d := CoverScale.initialDepth (Cube D) r n-1
      let copies := TeamScales.width n scales.α
      1+initialMass (D:=D) n r d copies headerFactor ≤ TeamScales.width n (1/2:ℝ) ∧
      GridHosts.tileCount axes d ≤ 2^(60*logWidth r n) ∧
      copies*DeckGrid.seedChannelWidth n r axes d < 2^(60*logWidth r n) := by
  let A := DeckGrid.seedPublicBase degree+12+810489*(11+2*degree)+(2*degree+1)+1
  obtain ⟨v,hv,record⟩ := eventually_seed_record_words S scales headerFactor A
  refine ⟨v,hv,?_⟩
  filter_upwards [record,eventually_offsets S scales,eventually_ge_atTop 1] with n haveBase offset hn
  intro r hr room gridDepth count
  let start := CoverScale.initialDepth (Cube D) r n
  let d := start-1
  let copies := TeamScales.width n scales.α
  let base := initialMass (D:=D) n r d copies headerFactor
  let H := DeckGrid.seedChannelWidth n r axes d
  let cap := DeckGrid.seedBoxCapacity n r axes d degree
  let dB := DeckGrid.seedDescriptionWidth n r axes d (headerFactor*logWidth r n) (BottomGridBank.bodyBudget cap)
  have hn' : 1≤(n:ℝ) := by exact_mod_cast hn
  have copies_pos : 1≤copies := Nat.le_floor (by simpa using Real.one_le_rpow hn' (by exact_mod_cast scales.alpha_pos.le))
  have depth_eq : d+1=start := by
    have hs : 1 ≤ start := Nat.succ_pos _
    dsimp only [d]; omega
  have hmass : base ≤ A*copies*(1+H+dB) := (DeckGrid.baseMass_scale n r axes d degree copies dB copies_pos).2
  have hbase := (haveBase r hr room base hmass).1
  have ufit : 2*n*r ≤ 2^(60*logWidth r n) :=
    (Nat.le_pow_clog (by decide : 1<2) _).trans
      (Nat.pow_le_pow_right (by decide) (by rw [←public_logWidth]; omega))
  have vtiles : GridHosts.tileCount axes d = CoverScale.sites (Cube D) start := by
    rw [←depth_eq]
    simp only [GridHosts.tileCount,CoverScale.sites,Fintype.card_fun,Fintype.card_fin]
  have vr := (offset r hr).2
  have nn : (n:ℝ)^(9/10:ℝ) ≤ n := by simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (9/10:ℝ)≤1)
  have vn : CoverScale.sites (Cube D) start ≤ r*n := by exact_mod_cast vr.trans (mul_le_mul_of_nonneg_left nn (by positivity))
  have hwidth : TeamScales.width n (1/2:ℝ) ≤ n := Nat.floor_le_of_le (by
    simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/2:ℝ)≤1))
  have hH : copies*H ≤ base := by
    have vH := Nat.le_mul_of_pos_left H (show 1 ≤ 2*degree+1 by omega)
    change copies*H ≤ DeckGrid.baseMass degree cap H copies dB
    unfold DeckGrid.baseMass
    exact (Nat.mul_le_mul_left copies (vH.trans (Nat.le_add_left ..))).trans (Nat.le_add_left ..)
  have nfit : n≤2*n*r := by nlinarith only [Nat.mul_le_mul_left n hr]
  exact ⟨hbase,vtiles.le.trans (vn.trans ((show r*n≤2*n*r by nlinarith only [Nat.zero_le (r*n)]).trans ufit)),
    (Nat.lt_of_le_of_lt hH (by omega : base<1+base)).trans_le (hbase.trans (hwidth.trans (nfit.trans ufit)))⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI

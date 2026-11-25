import OAI.Computability.BorderVNP.DiagonalSignedDemandCapacity
import OAI.Computability.BorderVNP.PackedNativeDemandLabels
import OAI.Computability.BorderVNP.DiagonalSignedDemandPacket

/-! # Selection of the signed cube placement on every attained public history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing PhysicalEpochs DeckGrid
open TeamScales Filter ExternalSew ParseBatch ParseBatchVerifier Prewire
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- One threshold supplies all numerical and structural assumptions of the
native conditional-mean placement on the selected signed startup's own rows. -/
theorem JointSchedule.eventually_signed_label_rows (b : JointSchedule s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
    let r := stretch b.ρ n
    let d := CoverScale.initialDepth (Cube D) r n-1
    let T := epochs s.τ n
    let copies := width n s.α
    let R := b.physical.teamsPred n
    ∀ work : ℕ, ∀ plan : SeedPlan S n r d T copies header work,
      ∃ count : (fan S)^T*copies=R+1, plan.SignedLabelRows count (b.physical.link n) a s.α ((s.τ:ℝ)/5) := by
  have α0 : 0 < (s.α:ℝ) := by exact_mod_cast s.alpha_pos
  have litPositive : 0 < 1-(s.α:ℝ)/3 := by linarith [s.alpha_small]
  have litLarge := ((tendsto_rpow_atTop litPositive).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  filter_upwards [b.eventually_signedSewnWidths (1/2) (by norm_num),b.eventually_signedSewnCellLoads header,
    b.eventually_geometricSeedStorage header,b.eventually_signed_grid,
    RoutingOutputs.NativeDemands.eventually_rows_budget α0 a s.label_slack.1 s.label_slack.2.1,litLarge]
    with n wires loads storage grid budget literalBig
  intro r d T copies R work plan
  obtain ⟨count,wire⟩ := wires header work plan
  obtain ⟨_,load⟩ := loads work plan
  refine ⟨count,?_⟩
  intro time pins inner Edge _ G lit order pos g len st W tag ns ne np sites edges ports table words ready dir
  have two : 2 ≤ literal s.α n := Nat.le_floor literalBig
  have half : 0 < (G.program.length+time)/2 := by rw [lit]; omega
  have hr : 0 < r := stretch_one ..
  have bounds : dir.DestinationBounds := by
    refine ⟨half,grid.2.1,hr,le_rfl,?_⟩
    simpa only [dir,freeDirectory,Directory.Layout.stride,Nat.add_sub_cancel,publicWidth] using
      GridHosts.gridRoom G (show 0<GridHosts.tileCount (Fintype.card (Cube D)) d from Fintype.card_pos)
  refine ⟨bounds,?_⟩
  intro bottom M q cells number state N cell old live ce cp edge port gap list recv
  obtain ⟨paid,wc,lc⟩ := plan.signed_directory_resources count G order pos W tag sites edges ports table words
    ready wire load number q
  have allTeams := (Nat.mul_comm copies ((fan S)^T)).trans count
  have tails : dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) := by
    change _ ≤ (R+1)*r*((G.program.length+time)/2)
    rw [←allTeams,lit]
    exact storage.2.2.2.2
  exact budget N cell edge port dir old live gap bounds _ _ (Nat.succ_pos R) (by decide : 0<2) tails lit
    paid (fun _ => rfl) wc lc

end Diagonal

end BorderVNP
end Computability
end OAI

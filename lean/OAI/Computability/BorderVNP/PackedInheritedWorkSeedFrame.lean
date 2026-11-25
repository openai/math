import OAI.Computability.BorderVNP.PackedInheritedWorkBottomPrep
import OAI.Computability.BorderVNP.PackedGroupedPortFrame
import OAI.Computability.BorderVNP.PackedInheritedWorkWrapped

/-! # The joint work, extent and geometry circuit at the grouped seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.WorkWords Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open Shortening.PreparedBins TeamContraction SelectedSchedule
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 500000
set_option maxRecDepth 3000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*TeamScales.logWidth r n
local notation "B" => boundary S (d+1)
local notation "O" => Pins S (d+1) B w 0
local notation "size₀" => seedSiteCapacity n r axes d
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "data₀" => AddressCircuit.ProductSlots axes (depth S (d+1) 0+1)
local notation "header" => WorkWords.grouped tiles extent

include plan in
private theorem seedFit : (B 0).sites ≤ 2^w := by
  rw [gridShape_zero]
  exact plan.fits

private abbrev endPin : Shortening.PublicEndpoints.Inputs (AddressCircuit.ProductSlots axes (depth S (d+1) 0+1))
    (B 0).sites (B 0).edges w w → O := fun j => .inr (.inr j)

variable {σ : Type} [Fintype σ] (base : Frame σ (Pins S (d+1) (boundary S (d+1)) (60*TeamScales.logWidth r n) 0))

/-- The physical seed initializer augmented by the two incidence passes for the real
one-copy fine and report padding. It is shared by every private verifier and table. -/
noncomputable def seedWidthFrame : Frame σ (OuterWidthPins S (d+1) B w 0) :=
  BottomPrep.frame (Geo := O) (Data := data₀) (V := (B 0).sites) (E := (B 0).edges)
    («w» := w) (n := tiles) base (endPin (n := n) (r := r) (d := d) S) header (seedFit S plan)
    (fun _ => true) copies (3*size₀) size₀

/-- The explicit cost of the geometric initializer and both width passes. -/
theorem seedWidthFrame_size : (seedWidthFrame S plan base).size ≤ base.size +
    2*Prep.charge (B 0).sites (B 0).edges tiles w :=
  BottomPrep.frame_size (Geo := O) (Data := data₀) (V := (B 0).sites) (E := (B 0).edges)
    («w» := w) (n := tiles) base (endPin (n := n) (r := r) (d := d) S) header (seedFit S plan)
    (fun _ => true) copies (3*size₀) size₀

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI

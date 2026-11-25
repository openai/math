import OAI.Computability.BorderVNP.PackedInheritedWorkMeasuredSeed
import OAI.Computability.BorderVNP.PackedFrozenBottomSeed
import OAI.Computability.BorderVNP.PackedFrozenSelectedSchemas

/-! # Initial frozen-row, geometry and width frame of the actual grouped seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar SelectedSchedule TeamScales
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2600000
set_option maxRecDepth 7500

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r n
local notation "B" => boundary S (d+1)
local notation "O" => Pins S (d+1) B w 0
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation3 "channels" => (groupedGridRows G axes d order position copies).edge
local notation3 "groups" => (Equiv.refl (Fin tiles)).toEmbedding
local notation3 "rs₀" => FrozenTape.Seed.rows n r order position channels groups copies
local notation3 "key₀" => order.symm.toEmbedding.trans (Fin.castLEEmb plan.fits)

/-- The initial physical immutable-row format before any choice of private
routed query witness, sidecar or coefficient table. -/
noncomputable abbrev seedFormat (copies : ℕ) := Format.bottom
  (FrozenTape.Seed.rows n r order position (groupedGridRows G axes d order position copies).edge groups copies) 0 w

variable {σ : Type} [Fintype σ] (base : Frame σ (Pins S (d+1) (boundary S (d+1)) (60*logWidth r n) 0))

local notation3 "fmt" => seedFormat G order position copies

/-- The actual initial public frame, sharing the geometric and width pass and
appending the literal original sparse records in the same physical row names. -/
noncomputable def seedTapeFrame : Frame σ (ProgramSchemas.outerPins S (d+1) w fmt 0) :=
  parallelFrame (seedWidthFrame S plan base) (Bottom.frame rs₀ 0 w key₀)

/-- Publishing the original sparse box references and ties adds at most two
constant gates to the real measured grouped-grid frame. -/
theorem seedTapeFrame_size :
    (seedTapeFrame S plan G order position base).size ≤ (seedWidthFrame S plan base).size+2 := by
  exact (parallelFrame_size (seedWidthFrame S plan base) (Bottom.frame rs₀ 0 w key₀)).le.trans
    (Nat.add_le_add_left (Bottom.frame_size (σ:=σ) rs₀ 0 w key₀) _)

/-- The gate coefficient and exponent at the base precede the verifier witness
and even its public input assignment. -/
theorem seedTapeFrame_rowWork (small : base.size ≤ 2) (edgeFit : (B 0).edges ≤ 2^w) (hL : 1 ≤ logWidth r n) :
    (seedTapeFrame S plan G order position base).size+1 ≤ rowWork (5+64000*66^3)
      (CoverScale.sites (Cube D) (d+1)) (logWidth r n) 3 (bottom (D:=D) (d+1)) := by
  have widths := seedWidthFrame_rowWork S plan base small edgeFit hL
  have two := seedTapeFrame_size S plan G order position base
  let vol := (bottom (D:=D) (d+1)).volume (CoverScale.sites (Cube D) (d+1))
  have vpos : 0 < vol := by unfold vol Shape.volume; omega
  have unit : 1 ≤ vol*(logWidth r n)^3 := Nat.mul_pos vpos (Nat.pow_pos hL)
  unfold rowWork at widths ⊢
  change _ ≤ (5+64000*66^3)*vol*(logWidth r n)^3
  have calcEq : (5+64000*66^3)*vol*(logWidth r n)^3 =
      (3+64000*66^3)*vol*(logWidth r n)^3 + 2*(vol*(logWidth r n)^3) := by ring
  rw [calcEq]
  change _ ≤ (3+64000*66^3)*vol*(logWidth r n)^3 at widths
  omega

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI

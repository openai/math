import OAI.Hierarchy.ProtocolRAMCalendarMarketTypes
import OAI.Hierarchy.ProtocolRAMStripTableTypes
import OAI.Hierarchy.ProtocolRAMPurchaseStage
import OAI.Hierarchy.ProtocolRAMOccurrenceHeader
import OAI.Hierarchy.ProtocolRAMCalendarMesh
import OAI.Hierarchy.ProbeShapeMenus

namespace OAI
/-! # The public board dimensions and the native occurrence header of each strip -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen PurchaseStage
open scoped Classical

/-- Actual resident tests, placement data and physical bank addresses of
one bounded local layout. The current predecessor stock address is
supplied separately at each chronological attempt. -/
structure Boards (z d k q digits ports : ℕ) where
  market : Calendar.Market z d k
  repair : Repair q ports
  test : StripTest digits
  globalTests : Calendar.GlobalTests.Layout
  baseline : ℝ
  price : Bank
  terms : Bank
  menu : Bank
  enabled : Bank
  selectors : Bank
  old : Bank
  reserve : Bank
  half : Bank
  cash : Bank
  report : Expr
  priceOut : ℕ→ℕ
  copies : ℕ
  maxWidth : ℕ
  start : ℕ
  indexBits : ℕ
  limit : ℕ

end Hierarchy.ProtocolRAM.StripDirectory

namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open PurchaseStage StripDirectory
open scoped Classical Fin.CommRing
variable {z d k q depth : ℕ}
attribute [local irreducible] permutationFabric
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R

set_option maxHeartbeats 1200000 in
/-- Static ingredients of the payload strip and the retained acquired strip.
The original outer shelf provides the physical acquired flags and tile addresses
for all subsequent reserve slices of that same trial. -/
structure Boards (z d k q depth : ℕ) where
  sampler : PurchaseSampler
  positive : 0<k
  radius : ℝ
  radius_nonneg : 0≤radius
  tolerance : ℝ
  tolerance_pos : 0<tolerance
  tree : Attempt → ℝ
  tree_nonneg : ∀ a,0≤tree a
  minimum : ℕ
  outer : ℕ → ℕ → StripDirectory.Boards z d k q
    (Fintype.card (PayloadStrip.Quotes (permutationFabric z d).shapes.length k)) (Fintype.card (PayloadRole (permutationFabric z d).shapes.length k))
  inner : ℕ → ℕ → ℕ → ℕ → StripDirectory.Boards z d k q
    (Fintype.card (ChainStrip.Axes depth k)) (Fintype.card (PurchasedRole depth k))
  stratumHeader : ℕ → ℕ → ℕ
  payloadEdge : ℕ → ℕ → Fin (Fintype.card (PayloadRole (permutationFabric z d).shapes.length k)) → Expr
  purchaseEdge : ℕ → ℕ → ℕ → ℕ → Fin (Fintype.card (PurchasedRole depth k)) → Expr

def start (s : Boards z d k q depth) : Attempt → ℕ
  | .outer p a => (s.outer p a).start
  | .inner p a j t => (s.inner p a j t).start

/-- Market rows enumerate every original stratum and every candidate path in
that stratum. Both kinds of attempt use the announced sampler and depth. -/
def header (F : Type*) [Field F]
    [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (s : Boards z d k q depth) (a : Attempt) : StockCommit.PortHeader :=
  ⟨start s a,PurchaseFrozen.count z d k * PurchaseFrozen.paths z s.sampler.degree depth,D⟩

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI

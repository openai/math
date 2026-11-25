import OAI.Hierarchy.ProtocolRAMCalendarStripHeader
import OAI.Hierarchy.ProbeStripPortGeometry

namespace OAI
/-! # Actual failure-ballot market assembled from the two strip forms -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open PurchaseStage StripDirectory PortPadding
open scoped Classical Fin.CommRing
variable {z d k q depth r edges w : ℕ}

local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R

variable (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

def shape (s : Boards z d k q depth) : Attempt → Geometry z d k q P R
  | .outer p a =>
    let b := s.outer p a
    let m := {b.market with sampler:=s.sampler,depth:=depth}
    payloadGeometry F depth s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
      (s.tree (.outer p a)) (s.tree_nonneg _) s.minimum {b with market:=m}
  | .inner p a j t =>
    let b := s.inner p a j t
    let m := {b.market with sampler:=s.sampler,depth:=depth}
    purchasedGeometry F depth (s.stratumHeader p a) (s.outer p a).market.shelf s.sampler
      s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos (s.tree (.inner p a j t))
      (s.tree_nonneg _) s.minimum {b with market:=m}

def build (s : Boards z d k q depth) (a : Attempt) (incoming : ℕ) : Format z d k q D :=
  (shape F s a).build (start s a) incoming

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI

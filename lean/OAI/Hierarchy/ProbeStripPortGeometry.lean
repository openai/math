import OAI.Hierarchy.ProbeShapeMenus
import OAI.Hierarchy.ProbeStripPlacedBoard
import OAI.Hierarchy.ProbeStripGeometryFormats

namespace OAI
/-! # The two actual strip catalogues in the homogeneous physical calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen PurchaseStage
open scoped Classical

variable {z d k q : ℕ}

local notation "N" => List.length (Fabric.shapes (permutationFabric z d))

def payloadGeometry (F : Type*) [Field F] (depth : ℕ) [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
    (hk : 0<k) (M : ℝ) (hM : 0≤M) (ε : ℝ) (he : 0<ε) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ)
    (B : Boards z d k q (Fintype.card (PayloadStrip.Quotes N k)) (Fintype.card (PayloadRole N k))) :
    PortPadding.Geometry z d k q (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k)) :=
  .payload (B.build (payloadFormat F z d k q hk M hM ε he tree ht minimum))
    (payloadChannels z N k).slot

def purchasedGeometry (F : Type*) [Field F] (depth header : ℕ) [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
    (sh : Shelf) (S : PurchaseSampler) (hk : 0<k) (M : ℝ) (hM : 0≤M)
    (ε : ℝ) (he : 0<ε) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ)
    (B : Boards z d k q (Fintype.card (ChainStrip.Axes depth k)) (Fintype.card (PurchasedRole depth k))) :
    PortPadding.Geometry z d k q (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k)) :=
  .purchased (B.build (purchasedFormat F z d k q depth header sh S hk M hM ε he tree ht minimum))
    (purchasedChannels (z:=z) (d:=d) (k:=k) sh S depth header).slot

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI

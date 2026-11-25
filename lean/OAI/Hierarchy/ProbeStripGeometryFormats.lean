import OAI.Hierarchy.ProbeStripCompiledFormat
import OAI.Hierarchy.ProbeShapeMenus

namespace OAI
/-! # The actual payload and purchased menu endpoint formats -/
noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen PurchaseStage
open scoped Classical Fin.CommRing

/-- Calendar installer for the actual payload strip, with its compulsory
payload chord, all signed rows and no purchased edge. -/
def payloadFormat (F : Type*) [Field F] (z d k q : ℕ)
    [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)]
    (hk : 0<k) (M : ℝ) (hM : 0≤M) (ε : ℝ) (he : 0<ε) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ) :=
  let stages := (permutationFabric z d).shapes.length
  let menu := payloadMenu F stages k hk M hM ε he tree ht minimum
  format (z:=z) (d:=d) (k:=k) (q:=q) (payloadChannels z stages k) menu

/-- Calendar installer for every native candidate after an acquisition. The
named strip has precisely its sampler links, signed altimeters and acquired
endpoint chord. The archived shelf supplies the candidate's CT tile words. -/
def purchasedFormat (F : Type*) [Field F] (z d k q depth start : ℕ)
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (sh : Shelf) (S : PurchaseSampler)
    (hk : 0<k) (M : ℝ) (hM : 0≤M) (ε : ℝ) (he : 0<ε) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ) :=
  let menu := purchasedMenu F depth k hk M hM ε he tree ht minimum
  format (z:=z) (d:=d) (k:=k) (q:=q) (purchasedChannels (z:=z) (d:=d) sh S depth start) menu

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI

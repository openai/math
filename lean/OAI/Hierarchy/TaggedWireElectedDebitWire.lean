import OAI.Hierarchy.TaggedWireElectedSource
import OAI.Hierarchy.TaggedWireStripDebitWire

namespace OAI
/-! # The physical chord of each original native row port, including unused padded lanes -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open WireTelescope ChosenPackets ChosenPackets.RowRouting
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} {v : FixedProtocolFormat F k p q Q σ Λ}
  {h width : ℕ}
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "W" => wordBits h D copies
local notation "days" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "b" => (P).catalogue
local notation "siteCode" => (siteNumber h D k).toEmbedding
local notation "K" => siteLast h D k+1
local notation "payloadExtra" => LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N)
local notation "boughtExtra" => LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth)
local notation "payloadReq" => ColumnWires.demand (I:=PayloadStrip.Columns N) (H:=Fin (PayloadStrip.edgeCount N))
  (k:=k) (Sum.inl (α:=PayloadStrip.Quotes N k) (β:=Empty))
local notation "boughtReq" => ColumnWires.demand (I:=ChainStrip.Columns v.depth) (H:=Fin (ChainStrip.edgeCount v.depth))
  (k:=k) (Sum.inl (α:=ChainStrip.Axes v.depth k) (β:=Unit))

namespace ElectedSource
variable {π : Equiv.Perm (Fin (2^h))}
    {mark : Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)}
    {ends : Fin (v.widePlacement h width).catalogue.rows → Site h (2^v.W) k × Site h (2^v.W) k}
    {m : Memory (wordBits h (2^v.W) copies)} {a : Attempt} {i : ℕ}
    (z : v.ElectedSource h width π mark ends m a i)

def debitWire {ports : ℕ} (pad : Chord K) : Fin ports→Chord K := by
  cases z with
  | payload ph tr record index ordinal g material =>
    exact stripDebitWire pad (reportedRole (SiteDirectory.payloadParties (d:=D) (k:=k) π)
      (ColumnWires.ends (horizontal _) payloadExtra) record)
  | purchased ph tr sj it hp ht unique path index ordinal g material =>
    exact stripDebitWire pad (reportedRole (SiteDirectory.boughtParties π v.sampler (mark (v.earnedDay ph tr hp ht)) (unique _))
      (ColumnWires.ends (horizontal _) boughtExtra) path)

end ElectedSource
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

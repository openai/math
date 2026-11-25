import OAI.Hierarchy.TaggedWireElectedSource
import OAI.Hierarchy.TaggedWireEarnedLoop

namespace OAI
/-! # A genuine elected row assigns zero transport to a loop of the terminal catalogue -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
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

theorem routing_loop_zero (atom : v.widePacketMenuIndex h a) (rt : Fin (v.wideBallotParties h a))
    (mass : ℕ) (pad : Chord K) (hist : Histogram (Fin (z.placed atom rt).data.terms) mass)
    (e : Fin (b).rows) (loop : (ends e).1=(ends e).2) :
    let earned:=z.routing atom rt mass pad
    earned.install.load (earned.bits hist) (paidRow (g:=Fintype.card (Commodity (Fin (2^h)) N k)) e)=0 := by
  cases z with
  | payload ph tr record index address g stock =>
    exact g.tender_loop_zero SiteNaming.labels (fun j : Probe.PositiveDemand payloadReq atom.val.val => payloadReq j.val) rt ((v.payloadPacketMenu N).packet atom) mass pad hist e loop
  | purchased ph tr sj it hp ht unique path index address g stock =>
    exact g.tender_loop_zero SiteNaming.labels (fun j : Probe.PositiveDemand boughtReq atom.val.val => boughtReq j.val) rt (v.purchasePacketMenu.packet atom) mass pad hist e loop

end ElectedSource
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

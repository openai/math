import OAI.Hierarchy.ProbeFixedWidePacketBody
import OAI.Hierarchy.TaggedWirePacketMiddleFields

namespace OAI
/-! # Both original strip templates publish their concrete intermediate role records -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe Strip
open WireTelescope StripPaths ChosenPackets.RowRouting
open scoped Classical
variable {S : ProbeStage.PurchaseSampler} {h d k n D : ℕ} {A B : Type} [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
def StripPorts.catalogueMiddle (p : StripPorts S h d k C (Fin n) B) (extra : A⊕B→DistinctPair X)
    (b : Board) (shift : ℕ) (site : X→Expr) (stock : A→Expr) (qty : R⊕T→Expr)
    (M : ℕ) (participant : X) : Fin (PacketTurns.middleColumns M)→Expr :=
  let enum:=treeFirst R T
  let o:=menuInputs extra enum site (readPrimary stock shift (p.primary b)) (emitterMate (A:=A) p b shift)
    (emitterTree (A:=A) p b shift) qty
  o.middleFields M (site participant)
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles
open Strip StripChart StripDirectory CatalogueRows WideCPU WireTelescope
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width
local notation "M" => v.widePacketRoles h
local notation "shift" => Fintype.card (Commodity (Fin (2^h)) N k)
def widePacketMiddle (a : Attempt) (siteROM : ℕ)
    (i : Fin (v.wideBallotParties h a)) : Fin (PacketTurns.middleColumns M)→Expr := by
  cases a with
  | outer phase trial=>
    let names : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) := SiteNaming.labels
    let party:=v.wideBallotSite P h width siteROM (.outer phase trial)
    exact (v.payloadPricePorts P h width).catalogueMiddle
      (LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N))
      (P).catalogue shift (party ∘ names) (v.widePayloadStored P h width phase trial)
      (v.widePayloadQty P h width phase trial) M (names.symm i)
  | inner phase trial layer tick=>
    let names : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
    let party:=v.wideBallotSite P h width siteROM (.inner phase trial layer tick)
    exact (v.purchasedPricePorts P h width phase trial).catalogueMiddle
      (LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth))
      (P).catalogue shift (party ∘ names) (v.widePurchaseStored P h width phase trial layer tick)
      (v.widePurchaseQty P h width phase trial layer tick) M (names.symm i)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

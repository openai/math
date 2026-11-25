import OAI.Hierarchy.TaggedWidePacketWantedFields
import OAI.Hierarchy.ProbeFixedWidePacketShape
import OAI.Hierarchy.TaggedWirePacketCatalogueControls
import OAI.Hierarchy.TaggedWireEarnedStock
import OAI.Hierarchy.TaggedWireEarnedQuantities

namespace OAI
/-! # Both actual strip ballots publish native install and low-carry columns -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles
open Strip StripChart StripDirectory CatalogueRows WideCPU WireTelescope
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width
local notation "M" => v.widePacketRoles h
local notation "D" => v.widePacketDegree
local notation "rows" => v.widePacketPhysical h width
local notation "sz" => v.widePacketShelf h
local notation "fs" => v.nativeFormats P h width
local notation "shift" => Fintype.card (Commodity (Fin (2^h)) N k)

def widePacketGate (a : Attempt) (siteROM : ℕ) (siteStride : Bank) (postStart : ℕ)
    (i : Fin (v.wideBallotParties h a)) : Fin ((M*3)*5+D)→Expr := by
  cases a with
  | outer phase trial=>
    let names : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) := SiteNaming.labels
    let party:=v.wideBallotSite P h width siteROM (.outer phase trial)
    exact (v.payloadPricePorts P h width).catalogueControls
      (LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N))
      (P).catalogue shift (party ∘ names) (v.widePayloadStored P h width phase trial)
      (v.widePayloadQty P h width phase trial) M rows postStart sz bits siteStride (names.symm i)
  | inner phase trial layer tick=>
    let names : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
    let party:=v.wideBallotSite P h width siteROM (.inner phase trial layer tick)
    exact (v.purchasedPricePorts P h width phase trial).catalogueControls
      (LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth))
      (P).catalogue shift (party ∘ names) (v.widePurchaseStored P h width phase trial layer tick)
      (v.widePurchaseQty P h width phase trial layer tick) M rows postStart sz bits siteStride (names.symm i)

def widePacketLowBefore (a : Attempt) (siteROM : ℕ) (siteStride : Bank) (preStart : ℕ)
    (i : Fin (v.wideBallotParties h a)) (q : Fin D) : Expr := by
  let party:=v.wideBallotSite P h width siteROM a
  let here:=party i
  let w:=pageRead (DatedRoleSheets.bank rows preStart sz bits 0) siteStride here q
  let other:=pageRead (DatedRoleSheets.bank rows preStart sz bits 2) siteStride here q
  let tag:=v.earnedTag P h width a
  cases a with
  | outer phase trial=>
    letI : Nonempty (PayloadRole N k):=⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    exact SiteDirectory.wantField (v.payloadPacketMenu N) (fs (.outer phase trial)).histMass
      party tag here w other
  | inner phase trial layer tick=>
    letI : Nonempty (PurchasedRole v.depth k):=⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    exact SiteDirectory.wantField v.purchasePacketMenu (fs (.inner phase trial layer tick)).histMass
      party tag here w other

/-- Each original opposite party has one lookup in the released neighbor table. -/
def wideSignedSocketKey (a : Attempt) (siteROM : ℕ) (siteStride : Bank) (preStart : ℕ)
    (i j : Fin (v.wideBallotParties h a)) : Expr :=
  let party:=v.wideBallotSite P h width siteROM a
  let widths : Fin D→Expr := pageRead (DatedRoleSheets.bank rows preStart sz bits 0) siteStride (party i)
  let others : Fin D→Expr := pageRead (DatedRoleSheets.bank rows preStart sz bits 2) siteStride (party i)
  PacketNeighbor.selectExpr widths others (party j)

def widePacketBody (a : Attempt) (siteROM : ℕ) (siteStride : Bank) (preStart postStart : ℕ)
    (i : Fin (v.wideBallotParties h a)) :
    Fin ((v.wideBallotShape P h width (.attempt a)).columns+((M*3)*5+(D+D)))→Expr :=
  packetFields ((v.wideFields P h width siteROM (.attempt a)).value i)
    (v.widePacketGate h width bits a siteROM siteStride postStart i)
    (v.widePacketLowBefore h width bits a siteROM siteStride preStart i)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI

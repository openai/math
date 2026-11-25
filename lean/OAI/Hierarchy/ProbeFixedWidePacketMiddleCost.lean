import OAI.Hierarchy.ProbeFixedWidePacketMiddle
import OAI.Hierarchy.TaggedWidePacketMenuFit
import OAI.Hierarchy.ProbeFixedWidePacketRates

namespace OAI
/-! # Bank residency and original per-field work of the signed middle reads -/
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
variable {W out : ℕ} (port : StripPorts S h d k (TreeColumn n) (Fin n) B)
    (extra : A⊕B→DistinctPair (TreeSite n k))
    (board : Board) (shift : ℕ) (site : TreeSite n k→Expr) (stock : A→Expr)
    (qty : (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k)→Expr)
    (M : ℕ) (who : TreeSite n k)
theorem StripPorts.catalogueMiddle_fits
    (src : ∀r:R,(port.primary board r).Fits W out) (sites : ∀x,(site x).Fits W out)
    (stored : ∀a,(stock a).Fits W out) (quantity : ∀u,(qty u).Fits W out)
    (f : Fin (PacketTurns.middleColumns M)) :
    (port.catalogueMiddle extra board shift site stock qty M who f).Fits W out := by
  apply PacketTurns.Operands.middleFields_fits
  · exact port.menu_resident extra board shift site stock qty src sites stored quantity
  · exact sites who

theorem StripPorts.catalogueMiddle_work {bound : ℕ} (enough : Fintype.card (R⊕T)≤M)
    (blocks : ∀c,(port.column c).work≤bound) (prim : ∀r:R,(port.primary board r).work≤bound)
    (mounted : ∀x,(site x).work≤bound) (held : ∀a,(stock a).work≤bound)
    (amount : ∀u,(qty u).work≤bound) (f : Fin (PacketTurns.middleColumns M)) :
    (port.catalogueMiddle extra board shift site stock qty M who f).work≤
      PacketTurns.Operands.middleValueRate M (baseBound bound) := by
  apply PacketTurns.Operands.middleFields_work
  · exact port.menu_bound extra board shift site stock qty blocks prim mounted held amount
  · exact enough
  · have h:=mounted who
    unfold baseBound
    omega
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
def PacketOperandBanks (a : Attempt) (w out : ℕ) : Prop :=
  match a with
  | .outer phase trial=>
      (∀r:PayloadRole N k,((v.payloadPricePorts P h width).primary (P).catalogue r).Fits w out) ∧
      (∀u,(v.widePayloadStored P h width phase trial u).Fits w out) ∧
      (∀u,(v.widePayloadQty P h width phase trial u).Fits w out)
  | .inner phase trial layer tick=>
      (∀r:PurchasedRole v.depth k,((v.purchasedPricePorts P h width phase trial).primary (P).catalogue r).Fits w out) ∧
      (∀u,(v.widePurchaseStored P h width phase trial layer tick u).Fits w out) ∧
      (∀u,(v.widePurchaseQty P h width phase trial layer tick u).Fits w out)

theorem widePacketMiddle_fits {w out : ℕ} (a : Attempt) (siteROM : ℕ)
    (sites : ∀i,(v.wideBallotSite P h width siteROM a i).Fits w out)
    (source : v.PacketOperandBanks h width a w out) (i : Fin (v.wideBallotParties h a))
    (f : Fin (PacketTurns.middleColumns M)) : (v.widePacketMiddle h width a siteROM i f).Fits w out := by
  cases a with
  | outer phase trial =>
    apply StripPorts.catalogueMiddle_fits
    · exact source.1
    · exact fun _=>sites _
    · exact source.2.1
    · exact source.2.2
  | inner phase trial layer tick =>
    apply StripPorts.catalogueMiddle_fits
    · exact source.1
    · exact fun _=>sites _
    · exact source.2.1
    · exact source.2.2

theorem widePacketMiddle_work (a : Attempt) (siteROM : ℕ) (i : Fin (v.wideBallotParties h a))
    (f : Fin (PacketTurns.middleColumns M)) : (v.widePacketMiddle h width a siteROM i f).work≤
      PacketTurns.Operands.middleValueRate M (baseBound v.packetInputRate) := by
  have colBound:v.packetColumnRate≤v.packetInputRate:=by unfold packetInputRate;omega
  have stored:v.coordinateWork≤v.packetInputRate:=by unfold packetInputRate;omega
  have pp:=v.widePacket_site_rate h width siteROM a
  cases a with
  | outer phase trial=>
    let : Nonempty (PayloadRole N k):=⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    apply StripPorts.catalogueMiddle_work
    · exact Nat.le_max_left ..
    · exact fun c=>(v.payload_columns_bound h width c).trans colBound
    · exact v.payload_primary_bound h width phase trial
    · exact fun j=>pp _
    · exact fun u=>(v.payload_stored_work P h width phase trial u).trans stored
    · exact fun u=>(v.widePayloadQty_work P h width phase trial u).trans (by unfold packetInputRate;omega)
  | inner phase trial layer tick=>
    let : Nonempty (PurchasedRole v.depth k):=⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    apply StripPorts.catalogueMiddle_work
    · exact Nat.le_max_right ..
    · exact fun c=>(v.purchase_columns_bound h width phase trial c).trans colBound
    · exact v.purchase_primary_bound h width phase trial layer tick
    · exact fun j=>pp _
    · exact fun u=>(v.purchased_stored_work P h width phase trial layer tick u).trans stored
    · exact fun u=>(v.widePurchaseQty_work P h width phase trial layer tick u).trans (by unfold packetInputRate;omega)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

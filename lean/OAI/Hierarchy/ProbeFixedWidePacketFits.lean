import OAI.Hierarchy.ProbeFixedWidePacketMiddleCost
import OAI.Hierarchy.TaggedWidePacketMenuFit
import OAI.Hierarchy.TaggedWireSignedSocketKey
import OAI.Hierarchy.TaggedWireEarnedQuantities

namespace OAI
/-! # The paid selector, sites and all finite install fields use only resident banks -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles
open Strip StripChart StripDirectory CatalystArchive CatalogueRows WideCPU WireTelescope
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width
local notation "M" => v.widePacketRoles h
local notation "D" => v.widePacketDegree
local notation "fs" => v.nativeFormats P h width
local notation "sr" => v.widePacketPhysical h width
local notation "ss" => v.widePacketShelf h
variable {w out : ℕ} (siteROM : ℕ) (stride : Bank) (old next : ℕ)
local notation "fields" e:arg => v.widePacketFields h width bits e siteROM stride old next

theorem widePacket_base_fits (a : Attempt) (tag : (v.earnedTag P h width a).Fits w out)
    (counters : ∀j,((fs a).board.batch.field j).Fits w out)
    (i : Fin (v.wideBallotParties h a)) (f : Fin (v.wideBallotShape P h width (.attempt a)).columns) :
    ((v.wideFields P h width siteROM (.attempt a)).value i f).Fits w out := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun j=>counters j)) f
  · exact BoughtSockets.choose_fits_bound (v.menuCodes N) 1
      (fun j : Fin (v.menuCodes N)=>Expr.lit (j.val*v.wideBallotParties h a+i.val+1))
      (v.earnedTag P h width a) (fun _=>trivial) tag
  · exact ⟨trivial,trivial⟩

section
attribute [local irreducible] Expr.Fits widePacketRoles
set_option maxHeartbeats 1200000 in
private theorem packet_gate_fits (a : Attempt)
    (sites : ∀i,(v.wideBallotSite P h width siteROM a i).Fits w out)
    (source : v.PacketOperandBanks h width a w out) (dir : stride.Fits w out)
    (room : ∀f:Fin 3,(DatedRoleSheets.bank sr next ss bits f).Fits w out)
    (i : Fin (v.wideBallotParties h a)) (f : Fin ((M*3)*5+D)) :
    (v.widePacketGate h width bits a siteROM stride next i f).Fits w out := by
  cases a with
  | outer phase trial =>
    let names : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) := SiteNaming.labels
    let party := v.wideBallotSite P h width siteROM (.outer phase trial)
    let shift := Fintype.card (Commodity (Fin (2^h)) N k)
    let controls := (v.payloadPricePorts P h width).catalogueControls («D»:=D)
      (LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N)) (P).catalogue shift (party ∘ names)
      (v.widePayloadStored P h width phase trial) (v.widePayloadQty P h width phase trial) M sr next ss bits stride (names.symm i)
    have gateEq : v.widePacketGate h width bits (.outer phase trial) siteROM stride next i f = controls f := rfl
    have measured := (v.payloadPricePorts P h width).catalogueControls_fits («D»:=D) (W:=w) (out:=out)
      (LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N)) (P).catalogue shift (party ∘ names)
      (v.widePayloadStored P h width phase trial) (v.widePayloadQty P h width phase trial) M sr next ss bits stride (names.symm i)
      source.1 (fun x=>sites (names x)) source.2.1 source.2.2 room dir f
    exact @Eq.mpr _ _ (congrArg (Expr.Fits w out) gateEq) measured
  | inner phase trial layer tick =>
    let names : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
    let party := v.wideBallotSite P h width siteROM (.inner phase trial layer tick)
    let shift := Fintype.card (Commodity (Fin (2^h)) N k)
    let controls := (v.purchasedPricePorts P h width phase trial).catalogueControls («D»:=D)
      (LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth)) (P).catalogue shift (party ∘ names)
      (v.widePurchaseStored P h width phase trial layer tick) (v.widePurchaseQty P h width phase trial layer tick) M sr next ss bits stride (names.symm i)
    have gateEq : v.widePacketGate h width bits (.inner phase trial layer tick) siteROM stride next i f = controls f := rfl
    have measured := (v.purchasedPricePorts P h width phase trial).catalogueControls_fits («D»:=D) (W:=w) (out:=out)
      (LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth)) (P).catalogue shift (party ∘ names)
      (v.widePurchaseStored P h width phase trial layer tick) (v.widePurchaseQty P h width phase trial layer tick) M sr next ss bits stride (names.symm i)
      source.1 (fun x=>sites (names x)) source.2.1 source.2.2 room dir f
    exact @Eq.mpr _ _ (congrArg (Expr.Fits w out) gateEq) measured

end

set_option maxHeartbeats 1200000 in
private theorem packet_low_fits (a : Attempt)
    (tag : (v.earnedTag P h width a).Fits w out)
    (sites : ∀i,(v.wideBallotSite P h width siteROM a i).Fits w out)
    (dir : stride.Fits w out) (room : ∀f:Fin 3,(DatedRoleSheets.bank sr old ss bits f).Fits w out)
    (i : Fin (v.wideBallotParties h a)) (u : Fin D) :
    (v.widePacketLowBefore h width bits a siteROM stride old i u).Fits w out := by
  have ready (f : Fin 3) :
      (pageRead (DatedRoleSheets.bank sr old ss bits f) stride (v.wideBallotSite P h width siteROM a i) u).Fits w out :=
    page_fits _ _ _ _ (room f) dir (sites i)
  cases a
  all_goals
    unfold widePacketLowBefore
    apply SiteDirectory.wantField_fits
    · exact sites
    · exact tag
    · exact sites i
    · exact ready 0
    · exact ready 2

set_option maxHeartbeats 800000 in
theorem widePacket_fits (a : Attempt) (tag : (v.earnedTag P h width a).Fits w out)
    (counters : ∀j,((fs a).board.batch.field j).Fits w out)
    (sites : ∀i,(v.wideBallotSite P h width siteROM a i).Fits w out)
    (source : v.PacketOperandBanks h width a w out) (dir : stride.Fits w out)
    (before : ∀f:Fin 3,(DatedRoleSheets.bank sr old ss bits f).Fits w out)
    (after : ∀f:Fin 3,(DatedRoleSheets.bank sr next ss bits f).Fits w out)
    (i : Fin (v.wideBallotParties h a)) :
    ((fields (.attempt a)).selected i).Fits w out ∧ ((fields (.attempt a)).site i).Fits w out ∧
    ∀f,((fields (.attempt a)).value i f).Fits w out := by
  refine ⟨by rw [widePacket_selected];exact tag,by rw [widePacket_site];exact sites i,?_⟩
  let party:=v.wideBallotSite P h width siteROM a
  have ready (q:Fin D) (f:Fin 3) : (pageRead (DatedRoleSheets.bank sr old ss bits f) stride (party i) q).Fits w out:=
    page_fits _ _ _ _ (before f) dir (sites i)
  refine Fin.addCases (motive:=fun f=>((fields (.attempt a)).value i f).Fits w out) ?_ ?_
  · intro f
    apply (congrArg (Expr.Fits w out) (v.widePacket_sheet h width bits siteROM stride old next a i f)).mpr
    refine Fin.addCases (motive:=fun f=>(v.widePacketSheet h width bits a siteROM stride old next i f).Fits w out) ?_ ?_ f
    · intro f
      apply (congrArg (Expr.Fits w out) (v.wideSheet_body h width bits siteROM stride old next a i f)).mpr
      exact packetFields_fits
        ((v.wideFields P h width siteROM (.attempt a)).value i)
        (v.widePacketGate h width bits a siteROM stride next i)
        (v.widePacketLowBefore h width bits a siteROM stride old i)
        (v.widePacket_base_fits h width siteROM a tag counters i)
        (packet_gate_fits v h width bits siteROM stride next a sites source dir after i)
        (packet_low_fits v h width bits siteROM stride old a tag sites dir before i) f
    · intro other
      apply (congrArg (Expr.Fits w out) (v.wideSheet_socket h width bits siteROM stride old next a i other)).mpr
      exact PacketNeighbor.key_fits _ _ (party other) (sites other) (fun q=>ready q 0) (fun q=>ready q 2)
  · intro middle
    apply (congrArg (Expr.Fits w out) (v.widePacket_middle h width bits siteROM stride old next a i middle)).mpr
    exact v.widePacketMiddle_fits h width a siteROM sites source i middle

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI

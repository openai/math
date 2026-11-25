import OAI.Hierarchy.ProbeFixedWidePartyCapacity
import OAI.Hierarchy.ProbeFixedPartyIndex
import OAI.Hierarchy.ProbeFixedWidePartyTender
import OAI.Hierarchy.ProbeFixedElectedTurnFields
import OAI.Hierarchy.ProbeFixedElectedMiddle

namespace OAI
/-! # The selected local circuit in the native packet menu -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope ChosenPackets ChosenPackets.RowRouting PacketTurns
open scoped Classical Fin.CommRing

namespace FixedProtocolFormat.ElectedSource
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} {v : FixedProtocolFormat F k p q Q σ Λ}
    {h width : ℕ}
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "W" => wordBits h D copies
local notation "days" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "K" => siteLast h D k+1
local notation "fs" => v.nativeFormats P h width
local notation "b" => (P).catalogue
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "name" => (siteNumber h D k).toEmbedding
variable {π : Equiv.Perm (Fin (2^h))}
    {mark : Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)}
    {ends : Fin (v.widePlacement h width).catalogue.rows → Site h (2^v.W) k × Site h (2^v.W) k}
    {m : Memory (Native.wordBits h (2^v.W) Native.copies)} {a : Attempt} {i : ℕ}
    (z : v.ElectedSource h width π mark ends m a i) (at₀ : v.widePacketMenuIndex h a)
    (rt : Fin (v.wideBallotParties h a)) (pad : Chord (siteLast h (2^v.W) k+1)) (siteROM : ℕ)
local notation "fd" => v.wideFields P h width siteROM (.attempt a)
local notation "mass" => (fs a).histMass
local notation "R" => z.routing at₀ rt mass pad
local notation "phys" => installedRows π ends name pad

open HistoryRoles
local notation "M" => v.widePacketRoles h
local notation "degree" => v.widePacketDegree
local notation "roles" => Fintype.card (R).Roles
local notation "before" => (v.wideBallotShape P h width (.attempt a)).columns
local notation "middle" => PacketTurns.middleColumns M
local notation "J" => v.wideBallotParties h a
local notation "op" => z.operands at₀ rt pad siteROM

open PassMatrix PartyPins Probe Tagged
open LinearAlgebra.SpectralBooks.SiteTensor
variable {V : Type} [Fintype V]
local notation "Q₀" => z.placed at₀ rt
local notation "i₀" j => Fin.cast (z.parties at₀ rt).symm j
local notation "old" => (v.wideBallotShape P h width (.attempt a)).columns

local notation "payloadDemand" =>
  ColumnWires.demand (I:=PayloadStrip.Columns N) (H:=Fin (PayloadStrip.edgeCount N)) (k:=k)
    (Sum.inl (α:=PayloadStrip.Quotes N k) (β:=Empty))
local notation "chainDemand" =>
  ColumnWires.demand (I:=ChainStrip.Columns v.depth) (H:=Fin (ChainStrip.edgeCount v.depth)) (k:=k)
    (Sum.inl (α:=ChainStrip.Axes v.depth k) (β:=Unit))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- The fixed finite menu chooses a real incident selector tap and the same
tree-first input row order as the earned installation. -/
theorem menu_circuit (j : Fin (v.wideBallotParties h a)) :
    ∃ (tap : (portGraph (Q₀).sites).Port (i₀ j)) (edges : Fin roles→Chord (Q₀).sites)
      (tapFit : mass*(Q₀).data.selectorBits≤(Q₀).graph.chordWidths (fun _=>mass*(Q₀).data.selectorBits) tap.val.1),
      (∀t,Installs.starts (source:=(R).source) (R).order t=physicalChord (Q₀).place (edges t)) ∧
      (∀neighbor roleBits laneBits keyBits (read : ℕ→ℕ→V⊕Bool),
      v.signedPartyAt h width a neighbor roleBits laneBits keyBits read at₀ j =
      circuit («D»:=degree) (width:=neighbor) (p:=roleBits) (e:=laneBits) (digits:=keyBits)
        old (z.roles_fit at₀ rt pad) read (Q₀).data (Q₀).graph (i₀ j) tap edges tapFit) := by
  cases z with
  | payload ph tr r i row g held =>
    let src : v.ElectedSource h width π mark ends m (.outer ph tr) i := .payload ph tr r i row g held
    let names : TreeSite (PayloadStrip.edgeCount N) k≃Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)):=SiteNaming.labels
    let chosenPacket := (v.payloadPacketMenu N).packet at₀
    let multiplicity := (fs (.outer ph tr)).histMass
    let tap := hasTap names v.positive (multiplicity*chosenPacket.selectorBits) j
    refine ⟨tap.choose,localRows names (src.placed at₀ rt).edge,tap.choose_spec,?_,?_⟩
    · intro t
      exact strip_aligned names
        (ColumnWires.ends (Strip.horizontal (PayloadStrip.edgeCount N))
          (LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N)))
        (fun x : Probe.PositiveDemand payloadDemand at₀.val.val => payloadDemand x.val)
        (SiteDirectory.payloadParties (d:=D) (k:=k) π) r rt chosenPacket multiplicity
        (installedRows π ends (siteNumber h D k).toEmbedding pad) (g.installation pad) (g.ordinal pad) t
    · intros; rfl
  | purchased ph tr sj it hp ht u path i row g held =>
    let src : v.ElectedSource h width π mark ends m (.inner ph tr sj it) i := .purchased ph tr sj it hp ht u path i row g held
    let names : TreeSite (ChainStrip.edgeCount v.depth) k≃Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)):=SiteNaming.labels
    let chosenPacket := v.purchasePacketMenu.packet at₀
    let multiplicity := (fs (.inner ph tr sj it)).histMass
    let tap := hasTap names v.positive (multiplicity*chosenPacket.selectorBits) j
    refine ⟨tap.choose,localRows names (src.placed at₀ rt).edge,tap.choose_spec,?_,?_⟩
    · intro t
      exact strip_aligned names
        (ColumnWires.ends (Strip.horizontal (ChainStrip.edgeCount v.depth))
          (LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth)))
        (fun x : Probe.PositiveDemand chainDemand at₀.val.val => chainDemand x.val)
        (SiteDirectory.boughtParties (depth:=v.depth) π v.sampler (mark (v.earnedDay ph tr hp ht)) (u _))
        path rt chosenPacket multiplicity (installedRows π ends (siteNumber h D k).toEmbedding pad)
        (g.installation pad) (g.ordinal pad) t
    · intros; rfl

set_option maxHeartbeats 1400000 in
theorem short_walks (t : Fin roles) : (((R).install.steps (R).order) t).length≤2 := by
  cases z with
  | payload ph tr r i row g held =>
    exact g.tender_short SiteNaming.labels
      (fun x : Probe.PositiveDemand payloadDemand at₀.val.val => payloadDemand x.val)
      rt ((v.payloadPacketMenu N).packet at₀) (fs (.outer ph tr)).histMass pad t
  | purchased ph tr sj it hp ht u path i row g held =>
    exact g.tender_short SiteNaming.labels
      (fun x : Probe.PositiveDemand chainDemand at₀.val.val => chainDemand x.val)
      rt (v.purchasePacketMenu.packet at₀) (fs (.inner ph tr sj it)).histMass pad t

theorem selected_fuel : (Q₀).data.partyUnit (Q₀).Tree≤v.signedPartyFuel h a := by
  cases z with
  | payload ph tr r i row g held => exact (v.payloadPacketMenu N).signedFuel_at at₀
  | purchased ph tr sj it hp ht u path i row g held => exact v.purchasePacketMenu.signedFuel_at at₀

end FixedProtocolFormat.ElectedSource
end Hierarchy.ProtocolRAM.Calendar
end

end OAI

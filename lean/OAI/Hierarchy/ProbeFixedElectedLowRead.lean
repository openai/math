import OAI.Hierarchy.TaggedWireElectedOperands
import OAI.Hierarchy.TaggedWireEarnedColumns
import OAI.Hierarchy.ProbeFixedWidePacketFields

import OAI.Hierarchy.TaggedWidePacketWantedRead

namespace OAI
/-! # Requested and installed low widths of an elected packet at its original party -/
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

open LinearAlgebra.SpectralBooks.SiteTensor Probe Tagged
variable (selectorBits : ℕ) (stride : Bank) (preStart postStart : ℕ) (j : Fin (v.wideBallotParties h a))
local notation "fields" => v.widePacketFields h width selectorBits (.attempt a) siteROM stride preStart postStart
local notation "party" => v.wideBallotSite P h width siteROM a
local notation "here" => party j
local notation "preWidth" => pageRead (DatedRoleSheets.bank
  (v.widePacketPhysical h width) preStart (v.widePacketShelf h) selectorBits 0) stride here (d:=degree)
local notation "preNeighbor" => pageRead (DatedRoleSheets.bank
  (v.widePacketPhysical h width) preStart (v.widePacketShelf h) selectorBits 2) stride here (d:=degree)
local notation "postWidth" => pageRead (DatedRoleSheets.bank
  (v.widePacketPhysical h width) postStart (v.widePacketShelf h) selectorBits 0) stride here (d:=degree)
local notation "postNeighbor" => pageRead (DatedRoleSheets.bank
  (v.widePacketPhysical h width) postStart (v.widePacketShelf h) selectorBits 2) stride here (d:=degree)
local notation "s" => z.site j
variable (out : Memory (Native.wordBits h (2^v.W) Native.copies))
    (arg : Word (Native.wordBits h (2^v.W) Native.copies)) {cap : ℕ}
    {total : (portGraph (siteLast h (2^v.W) k+1)).Port (z.site j) → ℕ}
    (parts : PassiveWindow.Parts ((portGraph (siteLast h (2^v.W) k+1)).Port (z.site j))
      (Fin v.widePacketDegree) cap total)

/-- The posted pre-release field reads this menu's full active demand on the identified chord. -/
theorem low_wanted (sites : K≤2^W) (codes : 1+v.menuCodes N≤2^W)
    (auth : ((v.earnedTag P h width a).eval out arg).val=v.widePacketNumber h a at₀)
    (located : ∀t,(party t).eval out arg=((z.site t).val:Word W))
    (dated : NeighborReads out arg parts preWidth preNeighbor) (q : Fin degree) :
    (((fields).value j (v.widePacketLowColumn h width a false q)).eval out arg)=
      ((parts.owner q).elim 0 (fun p=>if 0<parts.width q then (z.placed at₀ rt).wants mass p.val.1 else 0):Word W) := by
  rw [v.widePacket_low_read]
  cases z with
  | payload ph tr r i row g held =>
    let : Nonempty (PayloadRole N k):=⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
    exact SiteDirectory.wantField_read (v.payloadPacketMenu N) _ _ out arg
      (SiteNaming.labels.symm.toEmbedding.trans (ballEmbedding (SiteDirectory.payloadParties (d:=D) (k:=k) π) r)) _ parts _ _ dated
      _ _ at₀ ((Nat.add_le_add_left (Nat.le_max_left ..) 1).trans codes) auth sites located (located j) q
  | purchased ph tr slice tick hp ht unique path i row g held =>
    let : Nonempty (PurchasedRole v.depth k):=⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
    exact SiteDirectory.wantField_read v.purchasePacketMenu _ _ out arg
      (SiteNaming.labels.symm.toEmbedding.trans (ballEmbedding (SiteDirectory.boughtParties π v.sampler (mark (v.earnedDay ph tr hp ht)) (unique _)) path)) _ parts _ _ dated
      _ _ at₀ ((Nat.add_le_add_left (Nat.le_max_right ..) 1).trans codes) auth sites located (located j) q

attribute [local irreducible] StripPorts.catalogueControls RowRouting.post

set_option maxHeartbeats 2000000 in
/-- The posted post-release field sums installed occurrence widths on that same physical chord. -/
theorem low_installed (hist : Histogram (Fin (z.placed at₀ rt).data.terms) mass)
    (geom : Reads (Installs.starts (source:=(R).source) (R).order) phys ((R).install.steps (R).order)
      (Installs.numbered (R).order ((R).bits hist)) op out arg)
    (sites : K≤2^W) (atSite : (here).eval out arg=((s).val:Word W))
    (dated : NeighborReads out arg parts postWidth postNeighbor) (q : Fin degree) :
    (((fields).value j (v.widePacketLowColumn h width a true q)).eval out arg)=
      ((parts.owner q).elim 0 (fun p=>if 0<parts.width q then (R).post hist p.val.1 else 0):Word W) := by
  rw [v.widePacket_low_read]
  cases z with
  | payload ph tr r i row g held =>
    let labels : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) := SiteNaming.labels
    let a:=Attempt.outer ph tr
    have sameSite :
        (v.wideBallotSite P h width siteROM a ∘ labels) (labels.symm j) =
          v.wideBallotSite P h width siteROM a j :=
      congrArg (v.wideBallotSite P h width siteROM a) (labels.apply_symm_apply j)
    have result:=g.tender_low («D»:=degree) labels (fun a : Probe.PositiveDemand
      (ColumnWires.demand (I:=PayloadStrip.Columns N) (H:=Fin (PayloadStrip.edgeCount N)) (k:=k)
        (Sum.inl (α:=PayloadStrip.Quotes N k) (β:=Empty))) at₀.val.val=>
      ColumnWires.demand (I:=PayloadStrip.Columns N) (H:=Fin (PayloadStrip.edgeCount N)) (k:=k)
        (Sum.inl (α:=PayloadStrip.Quotes N k) (β:=Empty)) a.val) rt ((v.payloadPacketMenu N).packet at₀)
      (fs a).histMass pad M (v.widePacketPhysical h width) postStart (v.widePacketShelf h) selectorBits stride
      (labels.symm j) (v.wideBallotSite P h width siteROM a ∘ labels) (v.widePayloadStored P h width ph tr)
      (v.widePayloadQty P h width ph tr) hist geom sites parts
      (by rw [sameSite]; exact dated)
      (by rw [sameSite]; exact atSite) q
    exact result
  | purchased ph tr sj it hp ht unique path i row g held =>
    let labels : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
    let a:=Attempt.inner ph tr sj it
    have sameSite :
        (v.wideBallotSite P h width siteROM a ∘ labels) (labels.symm j) =
          v.wideBallotSite P h width siteROM a j :=
      congrArg (v.wideBallotSite P h width siteROM a) (labels.apply_symm_apply j)
    have result:=g.tender_low («D»:=degree) labels (fun a : Probe.PositiveDemand
      (ColumnWires.demand (I:=ChainStrip.Columns v.depth) (H:=Fin (ChainStrip.edgeCount v.depth)) (k:=k)
        (Sum.inl (α:=ChainStrip.Axes v.depth k) (β:=Unit))) at₀.val.val=>
      ColumnWires.demand (I:=ChainStrip.Columns v.depth) (H:=Fin (ChainStrip.edgeCount v.depth)) (k:=k)
        (Sum.inl (α:=ChainStrip.Axes v.depth k) (β:=Unit)) a.val) rt (v.purchasePacketMenu.packet at₀)
      (fs a).histMass pad M (v.widePacketPhysical h width) postStart (v.widePacketShelf h) selectorBits stride
      (labels.symm j) (v.wideBallotSite P h width siteROM a ∘ labels) (v.widePurchaseStored P h width ph tr sj it)
      (v.widePurchaseQty P h width ph tr sj it) hist geom sites parts
      (by rw [sameSite]; exact dated)
      (by rw [sameSite]; exact atSite) q
    exact result

end FixedProtocolFormat.ElectedSource
end Hierarchy.ProtocolRAM.Calendar
end

end OAI

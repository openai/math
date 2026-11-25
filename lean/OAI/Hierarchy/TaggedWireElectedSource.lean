import OAI.Hierarchy.TaggedWireEarnedTender
import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.TaggedWideStripParties
import OAI.Hierarchy.ProbeFixedStoredRoleWords
import OAI.Hierarchy.ProbeFixedPrintedRole
import OAI.Hierarchy.ProbeStripAccounts
import OAI.Hierarchy.ProtocolRAMBoughtLocations
import OAI.Hierarchy.ProbeFixedPacketAtom
import OAI.Hierarchy.ProbeSelectedPacketWidths

namespace OAI
/-! # The installed strip selected by an original ballot row, before choosing its histogram -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
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

variable (v) in
def earnedDay (phase trial : ℕ) (p : phase<v.mesh.inject+v.mesh.cool) (t : trial<v.mesh.outerFuel) : Fin days :=
  finProdFinEquiv ((⟨phase,p⟩ : Fin (v.mesh.inject+v.mesh.cool)),(⟨trial,t⟩ : Fin v.mesh.outerFuel))

section Formation
variable (v h width)

private def electedEnds : Type := Fin (b).rows → Site h D k × Site h D k
private def electedMemory : Type := Memory W

private def purchasedPath (π : Equiv.Perm (Fin (2^h))) (mark : Marks h v.W k days)
    (phase trial : ℕ) (ph : phase<v.mesh.inject+v.mesh.cool) (tr : trial<v.mesh.outerFuel) : Type :=
  LiveChains v.sampler π v.depth (mark (v.earnedDay phase trial ph tr))

private def purchasedRow (π : Equiv.Perm (Fin (2^h))) (mark : Marks h v.W k days)
    (phase trial : ℕ) (ph : phase<v.mesh.inject+v.mesh.cool) (tr : trial<v.mesh.outerFuel)
    (path : purchasedPath v h π mark phase trial ph tr) : ℕ :=
  (BoughtLocation.relative (S:=v.sampler) (π:=π) (depth:=v.depth)
    (marked:=mark (v.earnedDay phase trial ph tr)) path).val

private def payloadInstallation (π : Equiv.Perm (Fin (2^h))) (ends : electedEnds v h width)
    (m : electedMemory v h) (r : Fin (2^h)) (i : ℕ) : Type :=
  EarnedInstall (sam:=v.sampler) (h:=h) (d:=D) (k:=k) (n:=PayloadStrip.edgeCount N) («K»:=K) (w:=W)
    (v.payloadPricePorts P h width) b π payloadExtra (SiteDirectory.payloadParties (d:=D) (k:=k) π)
    r ends siteCode (PayloadStrip.rowAddress r) m (i:Word W)

private def payloadStock (m : electedMemory v h) (phase trial : ℕ) (r : Fin (2^h)) (i : ℕ) : Prop :=
  ∀ j, (v.widePayloadStored P h width phase trial j).eval m (i:Word W) =
    (PurchaseInventory.slot (PayloadStrip.rowAddress r j):Word W)

private def purchasedInstallation (π : Equiv.Perm (Fin (2^h))) (mark : Marks h v.W k days)
    (ends : electedEnds v h width) (m : electedMemory v h) (phase trial : ℕ)
    (ph : phase<v.mesh.inject+v.mesh.cool) (tr : trial<v.mesh.outerFuel) (u : Exclusive mark)
    (path : purchasedPath v h π mark phase trial ph tr) (i : ℕ) : Type :=
  EarnedInstall (sam:=v.sampler) (h:=h) (d:=D) (k:=k) (n:=ChainStrip.edgeCount v.depth) («K»:=K) (w:=W)
    (v.purchasedPricePorts P h width phase trial) b π boughtExtra
    (SiteDirectory.boughtParties π v.sampler (mark (v.earnedDay phase trial ph tr)) (u _))
    path ends siteCode (stripAddress v.sampler π v.depth (mark (v.earnedDay phase trial ph tr)) path) m (i:Word W)

private def purchasedStock (π : Equiv.Perm (Fin (2^h))) (mark : Marks h v.W k days)
    (m : electedMemory v h) (phase trial slice inner : ℕ)
    (ph : phase<v.mesh.inject+v.mesh.cool) (tr : trial<v.mesh.outerFuel)
    (path : purchasedPath v h π mark phase trial ph tr) (i : ℕ) : Prop :=
  ∀ j, (v.widePurchaseStored P h width phase trial slice inner j).eval m (i:Word W) =
    (PurchaseInventory.slot (stripAddress v.sampler π v.depth (mark (v.earnedDay phase trial ph tr)) path j):Word W)

-- In the generated heterogeneous constructor comparisons, the two installations
-- have independently chosen protocol parameters, paths, boards and memories.
attribute [local irreducible] electedEnds electedMemory purchasedPath purchasedRow
  payloadInstallation payloadStock purchasedInstallation purchasedStock

set_option genSizeOf false in
set_option genInjectivity false in
set_option genCtorIdx false in
/-- Keeps the original candidate ordinal, birth row, and its exact histogram-independent paid installation. -/
inductive ElectedSource (π : Equiv.Perm (Fin (2^h))) (mark : Marks h v.W k days)
    (ends : electedEnds v h width) (m : electedMemory v h) : Attempt→ℕ→Type
  | payload (phase trial : ℕ) (r : Fin (2^h)) (i : ℕ) (row : r.val=i)
      (g : payloadInstallation v h width π ends m r i) (stock : payloadStock v h width m phase trial r i) :
      ElectedSource π mark ends m (.outer phase trial) i
  | purchased (phase trial slice inner : ℕ) (ph : phase<v.mesh.inject+v.mesh.cool) (tr : trial<v.mesh.outerFuel)
      (u : Exclusive mark) (path : purchasedPath v h π mark phase trial ph tr) (i : ℕ)
      (row : purchasedRow v h π mark phase trial ph tr path = i)
      (g : purchasedInstallation v h width π mark ends m phase trial ph tr u path i)
      (stock : purchasedStock v h width π mark m phase trial slice inner ph tr path i) :
      ElectedSource π mark ends m (.inner phase trial slice inner) i

end Formation

attribute [reducible] electedEnds electedMemory purchasedPath purchasedRow
  payloadInstallation payloadStock purchasedInstallation purchasedStock

namespace ElectedSource
variable {π : Equiv.Perm (Fin (2^h))}
    {mark : Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)}
    {ends : Fin (v.widePlacement h width).catalogue.rows → Site h (2^v.W) k × Site h (2^v.W) k}
    {m : Memory (wordBits h (2^v.W) copies)} {a : Attempt} {i : ℕ}
    (z : v.ElectedSource h width π mark ends m a i)

def placed (atom : v.widePacketMenuIndex h a) (rt : Fin (v.wideBallotParties h a)) : Placed F K := by
  cases z with
  | payload phase trial r i row g stock =>
    exact stripPacket (n:=PayloadStrip.edgeCount N) (k:=k) SiteNaming.labels (ColumnWires.ends (horizontal _) payloadExtra) (fun a : Probe.PositiveDemand payloadReq atom.val.val=>payloadReq a.val)
      (SiteDirectory.payloadParties (d:=D) (k:=k) π) r rt ((v.payloadPacketMenu N).packet atom)
  | purchased phase trial slice inner ph tr u path i row g stock =>
    exact stripPacket (n:=ChainStrip.edgeCount v.depth) (k:=k) SiteNaming.labels (ColumnWires.ends (horizontal _) boughtExtra) (fun a : Probe.PositiveDemand boughtReq atom.val.val=>boughtReq a.val)
      (SiteDirectory.boughtParties π v.sampler (mark (v.earnedDay phase trial ph tr)) (u _)) path rt
      (v.purchasePacketMenu.packet atom)

theorem terms (atom : v.widePacketMenuIndex h a) (rt : Fin (v.wideBallotParties h a)) :
    (z.placed atom rt).data.terms=v.widePacketTerms h a atom := by cases z <;> rfl

def routing (atom : v.widePacketMenuIndex h a) (rt : Fin (v.wideBallotParties h a)) (count : ℕ)
    (pad : Chord K) : RowRouting (Row.packet (z.placed atom rt) count) (installedRows π ends siteCode pad) := by
  cases z with
  | payload phase trial r i row g stock => exact g.tender SiteNaming.labels (fun a : Probe.PositiveDemand payloadReq atom.val.val=>payloadReq a.val) rt ((v.payloadPacketMenu N).packet atom) count pad
  | purchased phase trial slice inner ph tr u path i row g stock => exact g.tender SiteNaming.labels (fun a : Probe.PositiveDemand boughtReq atom.val.val=>boughtReq a.val) rt (v.purchasePacketMenu.packet atom) count pad

/-- Physical number of the original party, in the same ordering used by the sparse scatter. -/
def site (j : Fin (v.wideBallotParties h a)) : Fin K := by
  cases z with
  | payload phase trial r i row g stock =>
    exact SiteDirectory.payloadParties (d:=D) (k:=k) π (r,SiteNaming.labels.symm j)
  | purchased phase trial slice inner ph tr u path i row g stock =>
    exact SiteDirectory.boughtParties π v.sampler (mark (v.earnedDay phase trial ph tr)) (u _)
      (path,SiteNaming.labels.symm j)

theorem parties (atom : v.widePacketMenuIndex h a) (rt : Fin (v.wideBallotParties h a)) :
    (z.placed atom rt).sites=v.wideBallotParties h a := by cases z <;> rfl

theorem placed_site (atom : v.widePacketMenuIndex h a) (rt j : Fin (v.wideBallotParties h a)) :
    (z.placed atom rt).place (j.cast (z.parties atom rt).symm)=z.site j := by cases z <;> rfl

end ElectedSource
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI

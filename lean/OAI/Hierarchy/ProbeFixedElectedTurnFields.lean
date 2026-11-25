import OAI.Hierarchy.TaggedWireElectedOperands
import OAI.Hierarchy.TaggedWireEarnedColumns
import OAI.Hierarchy.ProbeFixedWidePacketFields

namespace OAI
/-! # The actual five native turn instructions of the selected strip -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope ChosenPackets ChosenPackets.RowRouting PacketTurns
open scoped Classical Fin.CommRing

namespace CatalogueRows.EarnedInstall
open StripPaths Probe HistoryRoles
open LinearAlgebra.SpectralBooks.SiteTensor
variable {sam : PurchaseSampler} {h d k n K w D : ℕ} {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "shift" => Fintype.card G
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin K} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {name : Site h d k↪Fin K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
variable (g : EarnedInstall p b π extra place u endRow name addr m reg)
variable {F J : Type} [Field F] [Fintype J] (labels : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (req : J → ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k)
    (rt : Fin (Fintype.card (TreeSite n k))) (packet : Packet F (fun e=>@DistinctPair.chord _ _ ⟨labels⟩ (ColumnWires.ends (Strip.horizontal n) extra e)) req)
    (copies : ℕ)

variable (pad : Chord K) (M outerRows start shelf bits : ℕ) (stride : Bank)
    (party : Fin (Fintype.card (TreeSite n k))) (site : Fin (Fintype.card (TreeSite n k)) → Expr)
    (stock : A → Expr) (qty : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k → Expr)
local notation "physicalOps" => g.operands (site ∘ labels) stock qty
local notation "physicalOrder" => (g.tender labels req rt packet copies pad).ordinal
local notation "currentPage" => DatedRoleSheets.bank outerRows start shelf bits 0
local notation "neighborPage" => DatedRoleSheets.bank outerRows start shelf bits 2

set_option maxHeartbeats 1200000 in
private theorem numbered_tender (enough : Fintype.card U ≤ M) (slot : Fin (Fintype.card U*3)) (f : Fin 5) :
    p.catalogueControls extra b shift (site ∘ labels) stock qty M outerRows start shelf bits stride
        (labels.symm party)
        (((finProdFinEquiv (slot,f)).castLE (Nat.mul_le_mul_right 5 (Nat.mul_le_mul_right 3 enough))).castAdd D) =
      (physicalOps).column ((physicalOps).gatheredWords physicalOrder
        (pageRead currentPage stride (site party) (d:=D))
        (pageRead neighborPage stride (site party) (d:=D))) (site party) (finProdFinEquiv (slot,f)) := by
  let readAt (endpoint : Expr) := (physicalOps).column ((physicalOps).gatheredWords physicalOrder
    (pageRead currentPage stride endpoint (d:=D)) (pageRead neighborPage stride endpoint (d:=D)))
    endpoint (finProdFinEquiv (slot,f))
  have sameSite : (site ∘ labels) (labels.symm party) = site party :=
    congrArg site (labels.apply_symm_apply party)
  exact (g.tender_column (D:=D) labels req rt packet copies pad M outerRows start shelf bits stride
    (labels.symm party) (site ∘ labels) stock qty enough slot f).trans (congrArg readAt sameSite)

end CatalogueRows.EarnedInstall

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

theorem roles_fit : roles≤M := by
  cases z with
  | payload => exact Nat.le_max_left ..
  | purchased =>exact Nat.le_max_right ..

variable (selectorBits : ℕ) (stride : Bank) (preStart postStart : ℕ) (j : Fin (v.wideBallotParties h a))
local notation "fields" => v.widePacketFields h width selectorBits (.attempt a) siteROM stride preStart postStart
local notation "here" => v.wideBallotSite P h width siteROM a j
local notation "sheet" f => DatedRoleSheets.bank (v.widePacketPhysical h width) postStart (v.widePacketShelf h) selectorBits f
local notation "price" => pageRead (sheet 0) stride here (d:=degree)
local notation "other" => pageRead (sheet 2) stride here (d:=degree)

attribute [local irreducible] StripPorts.catalogueControls CatalogueRows.EarnedInstall.operands
  Operands.column Operands.gatheredWords wideBallotSite

set_option maxHeartbeats 2000000 in
theorem turnOperand (slot : Fin (roles*3)) (f : Fin 5) :
    let col:=finProdFinEquiv (slot,f)
    let small:=z.roles_fit at₀ rt pad
    let padded:=col.castLE (Nat.mul_le_mul_right 5 (Nat.mul_le_mul_right 3 small))
    (fields).value j (((Fin.natAdd before (padded.castAdd (degree+degree))).castAdd J).castAdd middle)=
      (op).column ((op).gatheredWords (R).ordinal price other) here col := by
  intro col small padded
  rw [v.widePacket_turn]
  cases z with
  | payload ph tr r i row g held =>
    let labels : TreeSite (PayloadStrip.edgeCount N) k ≃ Fin (Fintype.card (TreeSite (PayloadStrip.edgeCount N) k)) := SiteNaming.labels
    let a:=Attempt.outer ph tr
    exact CatalogueRows.EarnedInstall.numbered_tender («D»:=degree) g labels (fun a : Probe.PositiveDemand
      (ColumnWires.demand (I:=PayloadStrip.Columns N) (H:=Fin (PayloadStrip.edgeCount N)) (k:=k)
        (Sum.inl (α:=PayloadStrip.Quotes N k) (β:=Empty))) at₀.val.val=>
      ColumnWires.demand (I:=PayloadStrip.Columns N) (H:=Fin (PayloadStrip.edgeCount N)) (k:=k)
        (Sum.inl (α:=PayloadStrip.Quotes N k) (β:=Empty)) a.val) rt ((v.payloadPacketMenu N).packet at₀)
      (fs a).histMass pad M (v.widePacketPhysical h width) postStart (v.widePacketShelf h) selectorBits stride
      j (v.wideBallotSite P h width siteROM a) (v.widePayloadStored P h width ph tr)
      (v.widePayloadQty P h width ph tr) small slot f
  | purchased ph tr sj it hp ht unique path i row g held =>
    let labels : TreeSite (ChainStrip.edgeCount v.depth) k ≃ Fin (Fintype.card (TreeSite (ChainStrip.edgeCount v.depth) k)) := SiteNaming.labels
    let a:=Attempt.inner ph tr sj it
    exact CatalogueRows.EarnedInstall.numbered_tender («D»:=degree) g labels (fun a : Probe.PositiveDemand
      (ColumnWires.demand (I:=ChainStrip.Columns v.depth) (H:=Fin (ChainStrip.edgeCount v.depth)) (k:=k)
        (Sum.inl (α:=ChainStrip.Axes v.depth k) (β:=Unit))) at₀.val.val=>
      ColumnWires.demand (I:=ChainStrip.Columns v.depth) (H:=Fin (ChainStrip.edgeCount v.depth)) (k:=k)
        (Sum.inl (α:=ChainStrip.Axes v.depth k) (β:=Unit)) a.val) rt (v.purchasePacketMenu.packet at₀)
      (fs a).histMass pad M (v.widePacketPhysical h width) postStart (v.widePacketShelf h) selectorBits stride
      j (v.wideBallotSite P h width siteROM a) (v.widePurchaseStored P h width ph tr sj it)
      (v.widePurchaseQty P h width ph tr sj it) small slot f

theorem turn_bit (mem : Memory W) (arg : Word W) (fetch : ℕ→ℕ→Bool)
    (read : ∀(f : Fin (v.widePacketShape h width (.attempt a)).columns) (bit : ℕ),fetch f.val bit=(((fields).value j f).eval mem arg).val.testBit bit)
    (slot : Fin (roles*3)) (field : Fin 5) (bit : ℕ) :
    fetch (before+(finProdFinEquiv (slot,field)).val) bit=
      (((op).column ((op).gatheredWords (R).ordinal price other) here (finProdFinEquiv (slot,field))).eval mem arg).val.testBit bit := by
  let col:=finProdFinEquiv (slot,field)
  let padded:=col.castLE (Nat.mul_le_mul_right 5 (Nat.mul_le_mul_right 3 (z.roles_fit at₀ rt pad)))
  let f:=((Fin.natAdd before (padded.castAdd (degree+degree))).castAdd J).castAdd middle
  exact (read f bit).trans (congrArg (fun e : Expr=>(e.eval mem arg).val.testBit bit)
    (z.turnOperand at₀ rt pad siteROM selectorBits stride preStart postStart j slot field))

end FixedProtocolFormat.ElectedSource
end Hierarchy.ProtocolRAM.Calendar
end

end OAI

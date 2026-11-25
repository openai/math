import OAI.Hierarchy.ProbeFixedRepairSlot
import OAI.Hierarchy.ProbeFixedSelectedScore
import OAI.Hierarchy.ProbeFixedFailurePlacement
import OAI.Hierarchy.ProbeFixedPayloadPopulation
import OAI.Hierarchy.ProbeFixedPurchasedArchiveBuffers
import OAI.Hierarchy.ProbeFixedNativeStrips
import OAI.Hierarchy.ProbeFixedRowTiles
import OAI.Hierarchy.ProbeFixedStripCounts

namespace OAI
/-! # Selected physical port placements on the dated repair tapes -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard StripChart
open StockCommit PurchaseStage RepairHistogram CatalystArchive StripDirectory PurchaseFrozen CatalogueRows
open scoped BigOperators Classical Fin.CommRing
section DatedFunding
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open AdaptiveProbe.ColumnWires LinearAlgebra.SpectralBooks.ChordGraph
open ProbeStage StripDirectory PurchaseFrozen
variable {z d k D q : ℕ} {F : Type*} [Field F] [Nonempty (Fin k)]
local notation "stages" => (permutationFabric z d).shapes.length
variable (depth keyBase : ℕ) [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (sh : Shelf) (sampler : PurchaseSampler) (hk : 0<k) (M : ℝ) (hM : 0≤M)
  (eps : ℝ) (he : 0<eps) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ)
  (board : StripDirectory.Boards z d k q (Fintype.card (ChainStrip.Axes depth k)) (Fintype.card (PurchasedRole depth k)))
  (prior start : ℕ) (mem : Shelf.Mem z d)
variable [Nonempty (PurchasedRole depth k)]
local notation "sourceB" => board.build (purchasedFormat F z d k q depth keyBase sh sampler hk M hM eps he tree ht minimum) prior

local notation "W" => Native.wordBits z d Native.copies
variable (actualSize :
  let packetMenu := purchasedMenu F depth k hk M hM eps he tree ht minimum
  let rawBoard := board.build (purchasedFormat F z d k q depth keyBase sh sampler hk M hM eps he tree ht minimum) prior
  let channels := purchasedChannels (z:=z) (d:=d) (k:=k) sh sampler depth keyBase
  StripSizes rawBoard channels.slot start D (Fintype.card packetMenu.index) (PacketWidths.ofMenu packetMenu).maximum mem)
local notation "I" => StripInput.of_purchased depth keyBase sh sampler hk M hM eps he tree ht minimum
  board prior start mem actualSize

omit [Nonempty (Fin k)] [Nonempty (PurchasedRole depth k)] in
/-- Physical purchased operands use the installed shelf.  The flags retain
the stock pointer from the tape on which the purchase was registered. -/
private theorem purchased_dated_funding (π : Equiv.Perm (Fin (2^z))) (oldStock : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Shelf.Mem z d)
    (tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows (sh.L sampler depth key).source
      (Shelf.pathRows sampler π depth key) mem)
    (flags : StoredFlags {sh with stockBase := oldStock} sampler π depth phase T kind frozen mem k)
    (headers : (stratumHeader z d k sampler.degree depth keyBase).Loaded mem)
    (keys : count z d k ≤ 2^W) (room : (depth+1)*paths z sampler.degree depth ≤ 2^W)
    (whole : count z d k*paths z sampler.degree depth ≤ 2^W) (wide : 0<W)
    (active : ∀ j,j∈liveRows (I).ballot mem (sourceB).market.rows →
      j.val<(stratumHeader z d k sampler.degree depth keyBase).count ∧
        (flagBank sh sampler z d k depth).read mem (j.val:Word W) ≠ 0) : (I).Placed := by
  let h := stratumHeader z d k sampler.degree depth keyBase
  let R := ↥(liveRows (I).ballot mem (sourceB).market.rows)
  let Active := {j : Fin h.count // (flagBank sh sampler z d k depth).read mem (j.val:Word W) ≠ 0}
  let row : R ↪ Active := ⟨fun j =>
    ⟨⟨j.val.val,(active j.val j.property).1⟩,(active j.val j.property).2⟩,by
    intro a b same
    exact Subtype.ext (Fin.ext (congrArg (fun j : Active => j.val.val) same))⟩
  have width : PurchaseInventory.footprint z stages k ≤ 2^W :=
    (Nat.le_add_left _ _).trans (Nat.le_of_lt (I).bankFit)
  let dated : Shelf := {sh with stockBase := oldStock}
  obtain ⟨slots,read⟩ := purchased_slot_embedding dated sampler π depth keyBase hk phase T kind frozen mem
    tiles flags headers keys room whole wide width
  refine ⟨restrictPorts row slots, ?_⟩
  intro j a
  change ((allChainSlot (z:=z) (d:=d) sh sampler depth h a).eval mem (j.val.val:Word W)).val = _
  have address : allChainSlot (z:=z) (d:=d) sh sampler depth h a =
      allChainSlot (z:=z) (d:=d) dated sampler depth h a := rfl
  rw [address]
  exact read (row j) a

end DatedFunding

variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bs" => v.nativeBoards P z width
local notation "H" => v.publicHeader P z width
local notation "f" => v.nativeFormats P z width
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "FEE" => charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local notation "arena" => v.privateArena P z width

section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "t" => Calendar.time v.mesh v.finish ev
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
local notation "x" => v.payloadStageInput P z width r banks src tab dst owners phase trial entry fitted
local notation "π" => v.payloadStage_compile P z width r banks src tab dst owners phase trial entry fitted
variable (s : v.RepairSlot P z width r banks src tab dst owners (.outer phase trial) entry)
local notation "live" => s.slot.currentReady
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry s.layout live π
local notation "test" => v.payloadTest P z width phase trial

include fitted s in
omit [Nonempty (Fin k)] in
theorem payload_repair_live (j : Fin (f ev).market.rows) (keep : j∈(T).selected) :
      (f ev).market.failures.live.eval pre (j.val:Word W)≠0 := by
  intro asleep
  have high : (test).failure.cut<(test).failure.value pre j :=
    v.selected_high P z width r banks src tab dst owners ev entry s.layout live π s.threshold j keep j.isLt
  have zero : (test).failure.value pre j=0 := by
    change (test).failure.live.eval pre (j.val:Word W)=0 at asleep
    simp [FailureWords.value,FailureWords.effective,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,asleep]
  omega

attribute [local irreducible] permutationFabric
set_option cleanup.letToHave false
set_option maxHeartbeats 3000000 in
include fitted s in
omit [Nonempty (Fin k)] in
theorem payload_spill_placed
    : (x).Placed := by
  classical
  have active := v.payload_repair_live P z width r banks src tab dst owners phase trial entry fitted s
  unfold payloadStageInput
  apply payload_funding_placement (F:=F) (z:=z) (d:=2^v.W) (k:=k)
    (bs).positive (bs).radius (bs).radius_nonneg (bs).tolerance (bs).tolerance_pos
    ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum
    {(bs).outer phase trial with market :=
      {((bs).outer phase trial).market with sampler := (bs).sampler, depth := v.depth}}
    (resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (build F bs) ev)
    ((bs).outer phase trial).start stage fitted
  intro i kept
  apply v.payload_live_lt P z width phase trial pre i
  · exact i.isLt.trans_le (v.market_rows_fit P z width s.late ev)
  · exact active i kept

end

section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "pre" => (guard C ev).apply entry
local notation "checked" => postSnapshot ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => v.stage P z width r banks src tab dst owners ev entry
local notation "t" => Calendar.time v.mesh v.finish ev
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry)
local notation "x" => v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry fitted
local notation "π" => v.purchasedStage_compile P z width r banks src tab dst owners phase trial slice inner entry fitted
variable (s : v.RepairSlot P z width r banks src tab dst owners (.inner phase trial slice inner) entry)
local notation "live" => s.slot.currentReady
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry s.layout live π
local notation "test" => v.purchasedTest P z width phase trial slice inner
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

include fitted s in
omit [Nonempty (Fin k)] in
theorem purchased_repair_live (j : Fin (f ev).market.rows) (keep : j∈(T).selected) :
      (f ev).market.failures.live.eval pre (j.val:Word W)≠0 := by
  intro asleep
  have high : (test).failure.cut<(test).failure.value pre j :=
    v.selected_high P z width r banks src tab dst owners ev entry s.layout live π s.threshold j keep j.isLt
  have zero : (test).failure.value pre j=0 := by
    change (test).failure.live.eval pre (j.val:Word W)=0 at asleep
    simp [FailureWords.value,FailureWords.effective,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,asleep]
  omega

attribute [local irreducible] permutationFabric
set_option cleanup.letToHave false
attribute [local irreducible] purchased_row_archive
set_option maxHeartbeats 5500000 in
include fitted s in
omit [Nonempty (Fin k)] in
theorem purchased_spill_placed
    (perm : Equiv.Perm (Fin (2^z))) (headLow : (h₀).stop≤(arena).base v.mesh (.attempt ev))
    (born : PurchasedBirth sh S perm v.depth ((bs).stratumHeader phase trial) entry k)
    : (x).Placed := by
  classical
  let : Nonempty (PurchasedRole v.depth k) :=
    ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  have room := v.purchased_table_room z s.late
  let archive := v.purchased_row_archive P z width r banks src tab dst owners phase trial slice inner
    entry perm live headLow born
  have active := v.purchased_repair_live P z width r banks src tab dst owners phase trial slice inner entry fitted s
  have height := v.purchased_raw_rows P z width phase trial slice inner
  have positive : 0 < W := by rw [wordBits_linear]; omega
  unfold purchasedStageInput
  apply purchased_dated_funding (F:=F) (z:=z) (d:=2^v.W) (k:=k)
    v.depth ((bs).stratumHeader phase trial) sh S (bs).positive (bs).radius (bs).radius_nonneg
    (bs).tolerance (bs).tolerance_pos ((bs).tree ev) ((bs).tree_nonneg ev) (bs).minimum
    {(bs).inner phase trial slice inner with market :=
      {((bs).inner phase trial slice inner).market with sampler := (bs).sampler, depth := v.depth}}
    (resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (build F bs) ev)
    ((bs).inner phase trial slice inner).start stage fitted perm archive.stock
    archive.phase archive.heat archive.kind archive.frozen archive.stageTiles archive.stageFlags
    archive.stageHeader room.1 room.2.1 room.2.2.1 positive
  intro i kept
  let j : Fin (h₀).count := ⟨i.val, height ▸ i.isLt⟩
  refine ⟨j.isLt, ?_⟩
  change (flagBank sh S z (2^v.W) k v.depth).read stage (j.val:Word W) ≠ 0
  rw [archive.flagRead j]
  exact active i kept

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

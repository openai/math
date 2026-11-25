import OAI.Hierarchy.ProbeFixedAffirmativeRows
import OAI.Hierarchy.ProbeFixedPrintedTape
import OAI.Hierarchy.ProbeFixedSelectedScore
import OAI.Hierarchy.ProbeFixedSelectedEconomy
import OAI.Hierarchy.ProbeFixedPayloadPopulation
import OAI.Hierarchy.ProbeFixedRowTiles
import OAI.Hierarchy.ProbeFixedQuoteFrames

namespace OAI
/-! # Physical per-row witnesses for the two stock-commit settlements -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory
open CatalogueRows PortPadding CatalystArchive PurchaseStage PurchaseFrozen PurchaseCT
open scoped Classical Fin.CommRing
attribute [local irreducible] permutationFabric
set_option cleanup.letToHave false
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "bills" => v.issued P z width r banks src tab dst owners
local notation "fmt" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "keys" => v.cashKeys P z width r banks src tab dst owners
local notation "H" => v.publicHeader P z width
local notation "bh" => StripChart.header F (v.nativeBoards P z width)
local notation "bs" => v.nativeBoards P z width
local notation "board" => P.catalogue
local notation "Goods" => Commodity (Fin (2^z)) N k
local notation "s[" t "]" => publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W) t width v.precision

open ColumnWires CatalystArchive LinearAlgebra.SpectralBooks.ChordGraph in
/-- Transporting a compiled strip preserves the chosen occurrence and the physical price word. -/
private theorem aligned_price_word
    {α β ι η K : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype η] [Field K]
    {axes sites stages machineWidth height dimension terms ports : ℕ}
    [Nonempty (Fin sites)] [Nonempty (Fin axes)] [Nonempty (Role ι η (α ⊕ β) axes)]
    {cost tolerance tree : ℝ} {length : η → ℝ} {capacity : α → ℝ}
    {edge : Role ι η (α ⊕ β) axes → Chord sites}
    {menu : Probe.FixedMenu K edge
      (demand (I:=ι) («H»:=η) (k:=axes) (Sum.inl (α:=α) (β:=β)))
      ((fun y : α → ℝ => quote (I:=ι) (k:=axes) cost length (LocalCommodity.extraPrice (B:=β) y)) ''
        Set.Icc 0 capacity) tolerance tree stages}
    (x : CatalystArchive.StripInput («A»:=α) (B:=β) («C»:=ι) («H»:=η) (k:=axes)
      menu machineWidth height dimension terms ports)
    (nativeForm : Format height dimension axes terms ports) (batch : Batch terms ports) (tape : Memory machineWidth)
    (formatEq : x.form=nativeForm) (batchEq : x.ballot=batch) (tapeEq : x.mem=tape)
    (sourceRow : Fin x.raw.market.rows) (targetRow : Fin nativeForm.market.rows)
    (sameRow : sourceRow.val = targetRow.val) (field : Fin ports) (output : ℕ) :
    let sourceIndex := x.plan.enum ⟨sourceRow,field⟩
    let targetIndex := (x.alignedPlan nativeForm batch tape formatEq batchEq tapeEq).enum ⟨targetRow,field⟩
    sourceIndex.val = targetIndex.val ∧
      (((fresh x.form.pricedArea x.form.stockSource).native machineWidth x.raw.market.rows x.ballot).after
        x.mem (output + sourceIndex.val)).val =
      (((fresh nativeForm.pricedArea nativeForm.stockSource).native machineWidth nativeForm.market.rows batch).after
        tape (output + targetIndex.val)).val := by
  subst nativeForm batch tape
  have same : sourceRow = targetRow := Fin.ext sameRow
  subst targetRow
  exact ⟨rfl,rfl⟩

section
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "J" => PayloadStrip.Quotes N k
local notation "surface" => (bs).outer phase trial
local notation "old" => ({(surface).old with base:=(fmt ev).market.shelf.stockBase})
local notation "pre" => (guard C ev).apply entry
local notation "post" => postOutput ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => input ev entry
local notation "test" => v.payloadTest P z width phase trial
variable (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
local notation "x" => v.payloadStageInput P z width r banks src tab dst owners phase trial entry fitted
local notation "π" => v.payloadStage_compile P z width r banks src tab dst owners phase trial entry fitted
variable (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) (Attempt.outer phase trial)
    (v.nativeFormats P z width (Attempt.outer phase trial)).pricedArea (v.nativeFormats P z width (Attempt.outer phase trial)).stockSource
    (v.stamp P z width r banks src tab dst owners (Attempt.outer phase trial)) v.keepLimit width
    ((v.privateArena P z width).base v.mesh (.attempt (Attempt.outer phase trial))))
  (live : ready (v.nativeChart P z width r banks src tab dst owners) (.attempt (Attempt.outer phase trial)) entry)
include layout live in
omit [Nonempty (Fin k)] in
/-- The prepared strip uses the mounted chart and broadcast room of its actual date. -/
private theorem payload_read_room :
    ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).raw.market.rows (x).ballot).ready (x).mem ∧
      BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).raw.market.rows W := by
  change ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).form.market.rows (x).ballot).ready (x).mem ∧
    BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).form.market.rows W
  rw [v.payloadStage_format P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_ballot P z width r banks src tab dst owners phase trial entry fitted,
    v.payloadStage_memory P z width r banks src tab dst owners phase trial entry fitted]
  exact ⟨v.entered P z width r banks src tab dst owners ev entry live,
    fresh_broadcastRoom (fmt ev).pricedArea (fmt ev).stockSource (b ev) layout.inputs layout.window.room⟩

local notation "mount" => (v.payload_read_room P z width r banks src tab dst owners phase trial entry fitted layout live).1
local notation "bc" => (v.payload_read_room P z width r banks src tab dst owners phase trial entry fitted layout live).2
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry layout live π
local notation "B" => (A).bank.coordinates (v.nativeSlots P z width ev)
local notation "price[" t "]" => maximizer (B).a (B).M t (B).coefficient (B).box
  ((B).units width ((A).read (Succession v.mesh (.attempt ev)).1 entry))
local notation "cells[" m "," t "]" => QuoteCells (s[t]) m (surface).price (GlobalTests.offsets (surface).globalTests) old
  PurchaseInventory.slot PurchaseInventory.lane (fun i : Goods=>(entry ((A).stockAt ev i)).val) (JointHeader.scores P.joint z N k).stride

theorem payload_rowRead (row : Fin (fmt ev).market.rows) (keep : row∈(T).selected)
    (t : ℝ) (ht : 0<t) (cut : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (initial : (H).Resident pre) («public» : (H).Resident stage) (maxWord : (H).payload.maxWord<2^W)
    (first : cells[pre,t]) (second : cells[stage,t])
    (headBefore : (bh ev).stop≤(g ev).out) (room : (board).rows<2^W) (wide : 0<W)
    (order : Fin (board).coreRows≃Edges v.sampler z (2^v.W) k)
    (loaded : CoreLookup.Loaded P.routes.core order post)
    (codes : ∀f,(board).core.lengthCode.eval post ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W))
    (fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W)
    (global : PayloadStrip.Columns N → Columns z (2^v.W))
    (columns : ∀c,(((v.payloadPricePorts P z width).column c).eval post (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val)
    (horizontal : ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.payloadPricePorts P z width).horizontal e l).eval post (row.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e)
    : Nonempty ((x).RowRead mount bc (keys ev) (v.printedCharge P z width ev)
      (fun _ _=>v.cost.atAttempt ev) row price[t] (1/(v.precision:ℝ))) := by
  have high : (test).failure.cut<(test).failure.value pre row :=
    v.selected_high P z width r banks src tab dst owners ev entry layout live π cut row keep row.isLt
  have active : (fmt ev).market.failures.live.eval pre (row.val:Word W)≠0 := by
    intro asleep
    have zero : (test).failure.value pre row=0 := by
      change (test).failure.live.eval pre (row.val:Word W)=0 at asleep
      simp [FailureWords.value,FailureWords.effective,Expr.eval,
        ThreeFlat.RAM.DescriptorExpr.Comparison.test,asleep]
    omega
  have bound:=(live.2.2.2.2.2.1)
  change (repair C ev).repairBits.base+(fmt ev).market.rows<2^W at bound
  have roomAt : row.val<2^W := by omega
  have original:=v.payload_live_lt P z width phase trial pre row roomAt active
  let root : Fin (2^z):=⟨row.val,original⟩
  let hits:J→Goods:=PayloadStrip.rowAddress root
  have address (j : J) : ((x).addr j).eval stage (row.val:Word W)=(PurchaseInventory.slot (hits j):Word W) :=
    payloadSlot_read stage root j
  have packet:=v.payload_packet_read P z width r banks src tab dst owners phase trial entry t ht row original pre stage initial «public» maxWord first second high
  have legal:=v.payload_key_legal P z width bills ev t ht entry root
  let key:=v.rowKey P z width bills ev t ht entry hits
  let idx:J→Fin (fmt ev).coordinates:=fun a=>v.nativeSlots P z width ev (hits a)
  refine ⟨⟨idx,payloadGrid v.digitRadix v.precision key,legal,packet,?_,?_,?_⟩⟩
  · intro a
    have space:=(x).bankFit
    have ptr:=v.slot_index P z width ev (hits a)
    have inside:=(idx a).isLt
    change (v.nativeSlots P z width ev (hits a)).val=PurchaseInventory.slot (hits a) at ptr
    have safe : PurchaseInventory.slot (hits a)<2^W := by
      change (fmt ev).pricedArea.start+(fmt ev).coordinates<2^W at space
      change (v.nativeSlots P z width ev (hits a)).val<(fmt ev).coordinates at inside
      omega
    exact (congrArg Fin.val (address a)).trans ((Fin.val_cast_of_lt safe).trans ptr.symm)
  · exact v.payload_printed_tape P z width r banks src tab dst owners phase trial entry fitted layout live row idx headBefore room wide order loaded codes fits
      global columns horizontal
  · exact v.rowKey_box P z width bills ev t ht entry hits

end

section
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "J" => ChainStrip.Axes v.depth k
local notation "surface" => (bs).inner phase trial slice inner
local notation "old" => ({(surface).old with base:=(fmt ev).market.shelf.stockBase})
local notation "pre" => (guard C ev).apply entry
local notation "post" => postOutput ((C).layout ev) (repair C ev) (prepared C ev entry)
local notation "stage" => input ev entry
local notation "test" => v.purchasedTest P z width phase trial slice inner
variable (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase trial slice inner entry)
local notation "x" => v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry fitted
local notation "π" => v.purchasedStage_compile P z width r banks src tab dst owners phase trial slice inner entry fitted
variable (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) (Attempt.inner phase trial slice inner)
    (v.nativeFormats P z width (Attempt.inner phase trial slice inner)).pricedArea (v.nativeFormats P z width (Attempt.inner phase trial slice inner)).stockSource
    (v.stamp P z width r banks src tab dst owners (Attempt.inner phase trial slice inner)) v.keepLimit width
    ((v.privateArena P z width).base v.mesh (.attempt (Attempt.inner phase trial slice inner))))
  (live : ready (v.nativeChart P z width r banks src tab dst owners) (.attempt (Attempt.inner phase trial slice inner)) entry)
include layout live in
omit [Nonempty (Fin k)] in
/-- The prepared strip uses the mounted chart and broadcast room of its actual date. -/
private theorem purchased_read_room :
    ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).raw.market.rows (x).ballot).ready (x).mem ∧
      BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).raw.market.rows W := by
  change ((fresh (x).form.pricedArea (x).form.stockSource).native W (x).form.market.rows (x).ballot).ready (x).mem ∧
    BroadcastRoom (fresh (x).form.pricedArea (x).form.stockSource) (x).ballot (x).form.market.rows W
  rw [v.purchasedStage_format P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_ballot P z width r banks src tab dst owners phase trial slice inner entry fitted,
    v.purchasedStage_memory P z width r banks src tab dst owners phase trial slice inner entry fitted]
  exact ⟨v.entered P z width r banks src tab dst owners ev entry live,
    fresh_broadcastRoom (fmt ev).pricedArea (fmt ev).stockSource (b ev) layout.inputs layout.window.room⟩

local notation "mount" => (v.purchased_read_room P z width r banks src tab dst owners phase trial slice inner entry fitted layout live).1
local notation "bc" => (v.purchased_read_room P z width r banks src tab dst owners phase trial slice inner entry fitted layout live).2
local notation "T" => v.selectedTape P z width r banks src tab dst owners ev entry layout live π
local notation "B" => (A).bank.coordinates (v.nativeSlots P z width ev)
local notation "price[" t "]" => maximizer (B).a (B).M t (B).coefficient (B).box
  ((B).units width ((A).read (Succession v.mesh (.attempt ev)).1 entry))
local notation "cells[" m "," t "]" => QuoteCells (s[t]) m (surface).price (GlobalTests.offsets (surface).globalTests) old
  PurchaseInventory.slot PurchaseInventory.lane (fun i : Goods=>(entry ((A).stockAt ev i)).val) (JointHeader.scores P.joint z N k).stride
local notation "sh" => ((bs).outer phase trial).market.shelf
local notation "S" => (bs).sampler
local notation "h₀" => stratumHeader z (2^v.W) k (S).degree v.depth ((bs).stratumHeader phase trial)

local notation "portCount" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "stripTape" => (fresh (x).form.pricedArea (x).form.stockSource).tape
  (x).ballot (x).mem (x).plan mount bc (keys ev) (v.printedCharge P z width ev) (fun _ _ => v.cost.atAttempt ev)

/-- The billed strip and the installed tape read the same price word at this row and field. -/
private theorem purchased_row_weight (row : Fin (fmt ev).market.rows) (field : Fin portCount) :
    (stripTape).weight ((x).plan.enum ⟨row,field⟩) = (T).weight ((π).enum ⟨row,field⟩) := by
  have result := aligned_price_word (α := ChainStrip.Axes v.depth k) (β := Unit)
    (ι := ChainStrip.Columns v.depth) (η := Fin (ChainStrip.edgeCount v.depth)) (K := F)
    (axes := k) (machineWidth := W) (height := z) (dimension := 2^v.W) (ports := portCount)
    (v.purchasedStageInput P z width r banks src tab dst owners phase trial slice inner entry fitted)
    (fmt ev) (b ev) stage
    (v.purchasedStage_format P z width r banks src tab dst owners phase trial slice inner entry fitted)
    (v.purchasedStage_ballot P z width r banks src tab dst owners phase trial slice inner entry fitted)
    (v.purchasedStage_memory P z width r banks src tab dst owners phase trial slice inner entry fitted)
    row row rfl field (g ev).out
  let sourceIndex : Fin (fmt ev).pricedArea.occurrences := (x).plan.enum ⟨row,field⟩
  let targetIndex : Fin (fmt ev).pricedArea.occurrences := (π).enum ⟨row,field⟩
  have same : sourceIndex = targetIndex := by
    dsimp only [sourceIndex, targetIndex, purchasedStage_compile, taskCommit]
    exact Fin.ext result.1
  have charged := congrArg₂ (v.printedCharge P z width ev) same result.2
  exact charged

/-- All cash-only fields of this literal row carry their printed purchased prices. -/
private theorem purchased_row_printed (row : Fin (fmt ev).market.rows) (idx : J → Fin (fmt ev).coordinates)
    (headBefore : (bh ev).stop≤(g ev).out) (room : (board).rows<2^W) (wide : 0<W)
    (order : Fin (board).coreRows≃Edges v.sampler z (2^v.W) k)
    (loaded : CoreLookup.Loaded P.routes.core order post)
    (codes : ∀f,(board).core.lengthCode.eval post ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W))
    (fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W)
    (global : ChainStrip.Columns v.depth → Columns z (2^v.W))
    (columns : ∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval post (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val)
    (horizontal : ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval post (row.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e)
    (birth : (board).coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval post (row.val:Word W)).val)
    : ∀ role : PurchasedRole v.depth k, ColumnWires.account idx role = none →
      (stripTape).weight ((x).plan.enum
        ⟨row,PortPadding.inject (x).ports ((Fintype.equivFin (PurchasedRole v.depth k)) role)⟩) =
      ColumnWires.printed (bs).radius (ChainStrip.length v.depth) role := by
  intro role cash
  let ordinal := (Fintype.equivFin (PurchasedRole v.depth k)) role
  let billedField : Fin portCount := PortPadding.inject (x).ports ordinal
  let physicalField : Fin portCount := PortPadding.inject
    (Nat.le_max_right (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))) ordinal
  have sameField : billedField = physicalField := Fin.ext rfl
  let billedPrice (field : Fin portCount) : ℝ := (stripTape).weight ((x).plan.enum ⟨row,field⟩)
  let installedPrice (field : Fin portCount) : ℝ := (T).weight ((π).enum ⟨row,field⟩)
  have aligned : billedPrice billedField = billedPrice physicalField := congrArg billedPrice sameField
  have mounted : billedPrice physicalField = installedPrice physicalField :=
    v.purchased_row_weight P z width r banks src tab dst owners phase trial slice inner entry fitted layout live row physicalField
  have observed : installedPrice physicalField = ColumnWires.printed v.radius (ChainStrip.length v.depth) role :=
    v.purchased_printed_tape P z width r banks src tab dst owners phase trial slice inner entry fitted layout live
      row idx headBefore room wide order loaded codes fits global columns horizontal birth role cash
  have radiusAt : v.radius = (bs).radius := rfl
  have radiusPrice := congrArg (fun radius => ColumnWires.printed radius (ChainStrip.length v.depth) role) radiusAt
  exact aligned.trans (mounted.trans (observed.trans radiusPrice))

theorem purchased_rowRead (row : Fin (fmt ev).market.rows) (keep : row∈(T).selected)
    (t : ℝ) (ht : 0<t) (cut : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (initial : (H).Resident pre) («public» : (H).Resident stage) (maxWord : (H).bought.maxWord<2^W)
    (first : cells[pre,t]) (second : cells[stage,t]) (perm : Equiv.Perm (Fin (2^z))) (oldHeader : (h₀).Loaded pre) (nextHeader : (h₀).Loaded stage)
    (oldTiles : ∀ key : Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (Shelf.pathRows S perm v.depth key) pre)
    (nextTiles : ∀ key : Key z (2^v.W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((sh).L S v.depth key).source (Shelf.pathRows S perm v.depth key) stage)
    (rowLive : v.PurchasedLiveRow P z width phase trial slice inner perm row)
    (late : v.stripHeight≤z)
    (headBefore : (bh ev).stop≤(g ev).out) (room : (board).rows<2^W) (wide : 0<W)
    (order : Fin (board).coreRows≃Edges v.sampler z (2^v.W) k)
    (loaded : CoreLookup.Loaded P.routes.core order post)
    (codes : ∀f,(board).core.lengthCode.eval post ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W))
    (fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W)
    (global : ChainStrip.Columns v.depth → Columns z (2^v.W))
    (columns : ∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval post (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val)
    (horizontal : ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval post (row.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e)
    (birth : (board).coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval post (row.val:Word W)).val)
    : Nonempty ((x).RowRead mount bc (keys ev) (v.printedCharge P z width ev)
      (fun _ _=>v.cost.atAttempt ev) row price[t] (1/(v.precision:ℝ))) := by
  have high : (test).failure.cut<(test).failure.value pre row :=
    v.selected_high P z width r banks src tab dst owners ev entry layout live π cut row keep row.isLt
  have rooms:=v.purchased_table_room z late
  obtain ⟨hits,signed,atFirst,address⟩:=v.purchased_raw_slots P z width phase trial slice inner perm pre stage
    oldHeader nextHeader oldTiles nextTiles rooms.1 rooms.2.1 row rowLive
  have packet:=v.purchased_packet_read P z width r banks src tab dst owners phase trial slice inner entry t ht row hits pre stage initial «public» maxWord first second
    atFirst address signed high
  have legal:=v.purchased_key_legal P z width bills ev t ht entry hits signed
  let key:=v.rowKey P z width bills ev t ht entry hits
  let idx:J→Fin (fmt ev).coordinates:=fun a=>v.nativeSlots P z width ev (hits a)
  refine ⟨⟨idx,gridAxes v.digitRadix v.precision key,legal,packet,?_,?_,?_⟩⟩
  · intro a
    have space:=(x).bankFit
    have ptr:=v.slot_index P z width ev (hits a)
    have inside:=(idx a).isLt
    change (v.nativeSlots P z width ev (hits a)).val=PurchaseInventory.slot (hits a) at ptr
    have safe : PurchaseInventory.slot (hits a)<2^W := by
      change (fmt ev).pricedArea.start+(fmt ev).coordinates<2^W at space
      change (v.nativeSlots P z width ev (hits a)).val<(fmt ev).coordinates at inside
      omega
    exact (congrArg Fin.val (address a)).trans ((Fin.val_cast_of_lt safe).trans ptr.symm)
  · exact v.purchased_row_printed P z width r banks src tab dst owners phase trial slice inner entry
      fitted layout live row idx headBefore room wide order loaded codes fits global columns horizontal birth
  · exact v.rowKey_box P z width bills ev t ht entry hits

end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

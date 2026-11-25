import OAI.Hierarchy.ProbeFixedCatalystHeaders
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCatalystPurchasedOrigin
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMaster

namespace OAI
/-! # The original bought shelf in the fixed native event arena -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart CoreBoard CatalystArchive
open BoughtSockets CatalogueRows PurchaseFrozen
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel

/-- The inventory, score, two pricing, and empty-reserve pages all precede
every native private slab. -/
theorem catalyst_ports_le_first (P : v.Placement) (z width : ℕ) :
    (v.publicHeader P z width).ports.stop≤(v.privateArena P z width).first := by
  let s:=v.sized (v.seed P z width) width
  let E:=v.publicHeader P z width
  let charge:=StripChart.charges F s v.cost E.stop
  let reserve:=v.emptyReserve P z width
  have h : E.Ordered:=economic_ordered F s v.cost v.mesh (P).joint (P).catalogue (P).routes
    v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  have left : E.stop≤charge.payload.stop := Nat.le_add_right ..
  have right : charge.payload.stop≤charge.stop := Nat.le_add_right ..
  have last : reserve.base≤(v.privateArena P z width).first := by
    exact (Nat.le_add_right ..).trans (v.emptyReserve_end_le_first P z width)
  exact (economic_ports_end E h).trans (left.trans (right.trans last))

theorem catalyst_initial_le_first (P : v.Placement) (z width : ℕ) :
    (P).joint.initial≤(v.privateArena P z width).first := by
  have score : (P).joint.initial≤JointHeader.stop (P).joint z (Stages z (2^v.W)) k (DeadlineROM.count v.mesh) :=
    (Nat.le_add_right ..).trans ((JointHeader.order (P).joint z (Stages z (2^v.W)) k).trans (Nat.le_add_right ..))
  exact score.trans ((Nat.le_add_right ..).trans (v.catalyst_ports_le_first P z width))

private theorem mask_before_column (base bits rows column : ℕ) : base ≤ PostLayout.column base bits rows column := by
  calc base ≤ base+2^bits := Nat.le_add_right ..
       _ ≤ base+2^bits+rows := Nat.le_add_right ..
       _ ≤ base+2^bits+rows+2 := Nat.le_add_right ..
       _ ≤ PostLayout.column base bits rows column := Nat.le_add_right ..

/-- At any native event all affirmative DFS flags are on tape before that
event's tests, hence also before its price output and the end of its slab. -/
theorem catalyst_birth_room (P : v.Placement) (z width : ℕ) (a : Attempt) :
    let A:=v.privateArena P z width
    let f:=v.nativeFormats P z width a
    let base:=(A).base v.mesh (.attempt a)
    base≤ min f.testsStart f.market.failures.base ∧ base≤f.market.shelf.firstBase ∧
      f.market.flags+f.market.rows≤base+(A).stride := by
  intro A f base
  have order := v.posted_attempt_order P z width a
  have mask : f.testsStart≤f.maskStart := by
    unfold Format.maskStart PostLayout.afterTests
    omega
  have verdict : f.maskStart≤f.board.verdict := mask_before_column _ _ _ _
  have columns:=f.chargeColumns
  have labels : f.board.verdict≤f.labelStart+f.pricedArea.occurrences := by
    unfold Format.labelStart
    omega
  exact ⟨le_min order.2.2 order.1,order.2.1,
    (mask.trans (verdict.trans (labels.trans columns.1))).trans (v.attempt_room P z width a)⟩

theorem catalyst_base_label (P : v.Placement) (z width : ℕ) (a : Attempt) :
    (v.privateArena P z width).base v.mesh (.attempt a)≤(v.nativeFormats P z width a).labelStart := by
  let f:=v.nativeFormats P z width a
  have before:=(v.catalyst_birth_room P z width a).1.trans (min_le_left _ _)
  have mask : f.testsStart≤f.maskStart := by unfold Format.maskStart PostLayout.afterTests; omega
  have verdict : f.maskStart≤f.board.verdict := mask_before_column _ _ _ _
  exact before.trans (mask.trans (verdict.trans (Nat.le_add_right ..)))

set_option cleanup.letToHave false in
set_option maxHeartbeats 600000 in
/-- Both the complete power-of-two flag lookup and each original source
column of the birth DFS precede the later inner event. -/
theorem catalyst_bought_bank_room (P : v.Placement) (z width p a j t : ℕ) :
    let s:=v.nativeBoards P z width
    let sh:=((s).outer p a).market.shelf
    let base:=(v.privateArena P z width).base v.mesh (.attempt (.inner p a j t))
    let flags:=StripDirectory.flagBank sh (s).sampler z (2^v.W) k v.depth
    flags.base+flags.size≤base ∧ ∀i : Key z (2^v.W) k,
      (sh.L (s).sampler v.depth i).source.base+(sh.L (s).sampler v.depth i).source.size≤base := by
  intro s sh base flags
  let outer:=Attempt.outer p a
  let A:=v.privateArena P z width
  let entry:=(A).base v.mesh (.attempt outer)
  let f:=v.nativeFormats P z width outer
  let S:=(s).sampler
  have later : entry+(A).stride≤base := by
    have ord : position v.mesh (.attempt outer)+1≤position v.mesh (.attempt (.inner p a j t)) := by
      change trialBase v.mesh p a+1 ≤ trialBase v.mesh p a+1+j*sliceSize v.mesh+t
      exact (Nat.le_add_right _ (j*sliceSize v.mesh)).trans (Nat.le_add_right _ t)
    have step:=Nat.mul_le_mul_right (A).stride ord
    rw [Nat.add_mul,Nat.one_mul] at step
    change (A).first+position v.mesh (.attempt outer)*(A).stride+(A).stride≤
      (A).first+position v.mesh (.attempt (.inner p a j t))*(A).stride
    omega
  have pads : f.market.flags+2*(f.market.rows+1)≤f.maskStart := by
    have sameRows {letters : ℕ} (boards : StripChart.Boards z (2^v.W) k letters v.depth) (stock : ℕ) :
        (build F boards outer stock).market.failures.rows = (build F boards outer stock).market.rows := rfl
    have failed : f.market.failures.rows = f.market.rows := sameRows s _
    change f.market.flags+2*(f.market.rows+1) ≤ f.market.flags+f.market.rows+1+
      (f.batch.tests.excess.rows+1)+(f.batch.tests.payload.rows+1)+(f.market.failures.rows+1)
    rw [failed]
    omega
  have cap : flags.size≤2*(f.market.rows+1) := by
    change ProtocolRAMPurchaseSampler.span (PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z S.degree v.depth)≤_
    rw [show f.market.rows=PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z S.degree v.depth from
      StripChart.candidate_count F v.mesh A (P).joint.initial s outer]
    exact ProtocolRAMPurchaseSampler.span_le _
  have verdict : f.maskStart≤f.board.verdict := mask_before_column _ _ _ _
  have labels : f.board.verdict≤f.labelStart+f.pricedArea.occurrences := by unfold Format.labelStart; omega
  have upper := (verdict.trans (labels.trans f.chargeColumns.1)).trans ((v.attempt_room P z width outer).trans later)
  have padded : flags.base+flags.size≤base := (Nat.add_le_add_left cap _).trans (pads.trans upper)
  refine ⟨padded,?_⟩
  intro i
  let L:=sh.L S v.depth i
  obtain ⟨_,_,_,_,_,source,gates,tape,last⟩:=L.regions
  have block : L.endAddress≤flags.base :=
    (sh.end_le S v.depth i Nat.one_le_two_pow).trans ((sh.final_after S v.depth i).trans (Nat.le_add_right ..))
  have sourceEnd : L.source.base+L.source.size ≤ L.endAddress := by omega
  exact sourceEnd.trans (block.trans ((Nat.le_add_right flags.base flags.size).trans padded))

/-- Whole sampler stage extent for the birth-specialized owner expression. -/
theorem catalyst_bought_stage_room (P : v.Placement) (z width p a j t : ℕ)
    (i : Key z (2^v.W) k) :
    let s:=v.nativeBoards P z width
    let sh:=((s).outer p a).market.shelf
    (sh.L (s).sampler v.depth i).endAddress≤(v.privateArena P z width).base v.mesh (.attempt (.inner p a j t)) := by
  intro s sh
  let flags:=StripDirectory.flagBank sh (s).sampler z (2^v.W) k v.depth
  have endAt : (sh.L (s).sampler v.depth i).endAddress≤flags.base :=
    (sh.end_le (s).sampler v.depth i Nat.one_le_two_pow).trans
      ((sh.final_after (s).sampler v.depth i).trans (Nat.le_add_right ..))
  exact endAt.trans ((Nat.le_add_right ..).trans (v.catalyst_bought_bank_room P z width p a j t).1)

/-- The logical tiles in the same physically padded source bank. -/
theorem catalyst_bought_archive_room (P : v.Placement) (z width p a j t : ℕ) :
    let s:=v.nativeBoards P z width
    let sh:=((s).outer p a).market.shelf
    let base:=(v.privateArena P z width).base v.mesh (.attempt (.inner p a j t))
    let flags:=StripDirectory.flagBank sh (s).sampler z (2^v.W) k v.depth
    flags.base+flags.size≤base ∧ ∀i : Key z (2^v.W) k,
      (sh.L (s).sampler v.depth i).source.base+(v.depth+1)*PurchaseFrozen.paths z (s).sampler.degree v.depth≤base := by
  intro s sh base flags
  have banks:=v.catalyst_bought_bank_room P z width p a j t
  refine ⟨banks.1,?_⟩
  intro i
  let S:=(s).sampler
  let L:=sh.L S v.depth i
  have countEq : L.candidates=PurchaseFrozen.paths z S.degree v.depth := L.candidates_eq
  have capSource : (v.depth+1)*PurchaseFrozen.paths z S.degree v.depth≤L.source.size := by
    rw [←countEq]
    exact (ProtocolRAMPurchaseSampler.lt_span _).le
  exact (Nat.add_le_add_left capSource _).trans (banks.2 i)

variable {K G H R : ℕ} (z width : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
  (socket : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
local notation "P" => v.catalystPlacement z K G H R b cat socket
local notation "s" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "forms" => v.nativeFormats P z width
local notation "h" => Public.keyHead v.sampler (P).routes.column z v.W k v.depth
local notation "core" => CoreRoute.stop v.sampler z v.W k n v.depth K G H R

/-- Native receipt for the selected outer birth at each bounded inner date.
The two inequalities on the master public ROM are its placement ahead of
the initial inventory in the single tape supplied to every event. -/
def catalyst_birth (r : ℕ) (banks : RouteSettlement.Banks) (src table dest : ℕ) (owners : Bank)
    (initial : Shelf.Mem z (2^v.W)) (π : Equiv.Perm (Fin (2^z))) (p a j t : ℕ) :
    let C:=v.nativeChart P z width r banks src table dest owners
    let origin:=entryMemory C initial (.outer p a)
    Calendar.mounted C (events v.mesh) initial → p<v.mesh.inject+v.mesh.cool → a<v.mesh.outerFuel →
    j<v.mesh.reserveSteps → t<v.mesh.innerFuel →
    heapEnd z (2^v.W) copies≤b.initial → core≤b.initial → CoreCatalogue.Geometry π origin (2^v.W) →
    (h).Loaded origin → PurchasedBirth ((s).outer p a).market.shelf (s).sampler π v.depth ((s).stratumHeader p a)
      (entryMemory C initial (.inner p a j t)) k := by
  intro C origin mounted hp ha hj ht heap coreEnd geometry loaded
  have first:=v.catalyst_initial_le_first P z width
  let ev:=Attempt.outer p a
  let base:=(A).base v.mesh (.attempt ev)
  have dated : (A).first≤base := Nat.le_add_right ..
  have border := (Public.borders v.sampler (P).routes.column z v.W k n v.depth).2
  have keyCore : (h).stop≤core := border.trans (Nat.le_add_right ..)
  have early : max (heapEnd z (2^v.W) copies) (h).stop≤base :=
    (max_le heap (keyCore.trans coreEnd)).trans (first.trans dated)
  have bounds:=v.catalyst_birth_room P z width ev
  have birth := pricedBirthFromBoard F s v.mesh cat (P).routes A b.initial v.finish (v.basePhase width)
    (feedColumns (N:=Stages z (2^v.W)) v.mesh A forms b.initial width v.keepLimit) (cat.sink r banks src table dest owners)
    cat.idBase (fun i=>(StripChart.header F s i).fieldTerm) (StripChart.id F s cat) initial p a j t π
  exact birth mounted hp ha hj ht geometry loaded (early.trans bounds.1) ((le_max_right _ _).trans (early.trans bounds.2.1))
    bounds.2.2 (fun e x hx=>(v.event_prefix P z width r banks src table dest owners e x hx).1)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

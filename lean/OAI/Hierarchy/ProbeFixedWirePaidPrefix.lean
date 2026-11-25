import OAI.Hierarchy.ProbeFixedPriorPaidCore
import OAI.Hierarchy.TaggedWireDatedLedger
import OAI.Hierarchy.TaggedWirePaidPrefixFrame

namespace OAI
/-! # The original paid-edge array at a changing calendar prefix -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
private theorem all_attempt_slices {z d k q goods r edges : ℕ} (fmt : Format z d k q goods)
    (sink : Sink r edges) (idBase : ℕ) (role : Expr) (ids : Fin goods → Expr)
    (tree core : Traversals) (bits : ℕ) (holds : PaidWidths.Slice → Prop)
    (direct : holds (PaidWidths.paidDirect fmt.pricedArea fmt.stockSource
      (fmt.labelSource sink idBase role ids)))
    (mate : ∀ u v, tree.catalystMate = some (u, v) →
      holds (PaidWidths.paidMate fmt.pricedArea fmt.stockSource u v))
    (broad : holds (PaidWidths.paidBroadcast fmt.pricedArea tree.positions tree.owner tree.parity
      tree.edge tree.sourceRow fmt.board.batch.copies bits))
    (spill : holds (PaidWidths.paidSpill fmt.pricedArea core.positions core.owner core.parity
      core.edge core.sourceRow)) :
    ∀ s ∈ fmt.paidSlices sink idBase role ids tree core bits, holds s := by
  intro s found
  cases hm : tree.catalystMate with
  | none =>
    simp [Format.paidSlices, Format.mateSlices, hm] at found
    rcases found with rfl | rfl | rfl
    · exact direct
    · exact broad
    · exact spill
  | some pair =>
    simp [Format.paidSlices, Format.mateSlices, hm] at found
    rcases found with rfl | rfl | rfl | rfl
    · exact direct
    · exact mate pair.1 pair.2 hm
    · exact broad
    · exact spill

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "f" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "banks" => TerminalLayout.settlement page stock
local notation "order" => wideRouteOrder h D k
local notation "route" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "recipe" => routeBanks start cnt r
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit

local notation "ownerBank" => sinkBank start cnt r (P).catalogue.rows
local notation "paidO" => v.catalystPairOwners P h width
local notation "paidP" => v.catalystPairParity P h width
local notation "floor" => (A).endAddress v.mesh
local notation "who" => v.nativeBoards P h width
local notation "tree" => v.nativeTrees P h width
local notation "sink" => (P).catalogue.sink r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) ownerBank

local notation "es" => events v.mesh
local notation "until" => fun e=>(A).base v.mesh e+(A).stride

local notation "rows" => (P).catalogue.rows
local notation "chk" => fun m=> checkedOut C floor m
local notation "memAt" => fun m j=> StockBound.state C m j
local notation "stamp" => fun a=>(f a).labelSource sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
  (StripChart.id F who (P).catalogue a)
local notation "regular" => fun a=> PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (stamp a)
local notation "secondary" => fun a u v'=> PaidWidths.paidMate (f a).pricedArea (f a).stockSource u v'
local notation "broadcasting" => fun (bits : ℕ) a=> PaidWidths.paidBroadcast (f a).pricedArea
  (tree a).positions (tree a).owner (tree a).parity (tree a).edge (tree a).sourceRow (f a).board.batch.copies bits

set_option maxHeartbeats 800000 in
/-- Combine the original transaction components at an elapsed calendar date.
Both spill cases read the true immutable route and their bounded archive
index. Only the direct, mate, and selector-tree native labels are supplied
by the branch-specific socket proofs. -/
theorem wire_prior_paid_event (π : Equiv.Perm (Fin (2^h))) (initial : Memory w) (bits : ℕ)
    (active : Calendar.mounted C es initial) (word : floor<2^w)
    (native : v.WideSpillSource h width π (chk initial))
    (menu : Fintype.card (Actions N k)≤2^w) (goods : Fintype.card (Commodity (Fin (2^h)) N k)≤2^w)
    (edges : rows≤2^w) (lanes : ∀l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^h<2^w)
    (t : Fin (es).length) (j : ℕ) (past : t.val < j) (last : j≤(es).length)
    (paired : ∀a : Attempt,(es).get t=.attempt a→∀e : Fin rows,
      (regular a).load (chk initial) e=(regular a).load (memAt initial j) e ∧
      ∀u v', (tree a).catalystMate=some (u,v')→
        (secondary a u v').load (chk initial) e=(secondary a u v').load (memAt initial j) e)
    (treeAt : ∀a : Attempt,(es).get t=.attempt a→∀e : Fin rows,
      (broadcasting bits a).load (chk initial) e=(broadcasting bits a).load (memAt initial j) e)
    (s : PaidWidths.Slice) (found : s∈v.wideEventSlices h width bits ((es).get t)) (e : Fin rows) :
    s.load (memAt initial j) e=s.load (chk initial) e := by
  symm
  have eventMem:=(es).get_mem t
  have conserved:=v.prior_paid_low h width initial active t j past last
  cases ev : (es).get t with
  | feed b =>
    rw [ev] at found conserved eventMem
    change s ∈ ((lay b).columns).map (fun c => c.paidSlice (v.paidFeedPath P h width route lay b c)) at found
    obtain ⟨c,member,rfl⟩:=List.mem_map.mp found
    exact v.prior_feed_load h width π _ _ native b eventMem conserved word edges lanes c member e
  | attempt a =>
    rw [ev] at found conserved eventMem
    change s∈(f a).paidSlices sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
      (StripChart.id F who (P).catalogue a) (tree a) (v.paidSpillPath P h width recipe route order a) bits at found
    exact all_attempt_slices (f a) sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
      (StripChart.id F who (P).catalogue a) (tree a) (v.paidSpillPath P h width recipe route order a) bits
      (fun sl => sl.load (chk initial) e = sl.load (memAt initial j) e)
      (paired a ev e).1 (paired a ev e).2 (treeAt a ev e)
      (v.prior_spill_load h width π (chk initial) (memAt initial j) native a eventMem conserved
        word menu goods edges e) s found

theorem wire_paid_preserved_of_events (initial : Memory w) (bits j : ℕ) (_last : j≤(es).length)
    (eventRead : ∀ t : Fin (es).length,t.val < j→∀s∈ v.wideEventSlices h width bits ((es).get t),
      ∀e : Fin rows,s.load (memAt initial j) e=s.load (chk initial) e) (e : Fin rows) :
    v.wirePaidAt h width bits j (memAt initial j) e=v.wirePaidAt h width bits j (chk initial) e := by
  apply PaidWidths.total_rows_congr
  intro s member edge
  obtain ⟨ev,scheduled,found⟩:=List.mem_flatMap.mp member
  obtain ⟨n,hn,atDate⟩:=List.mem_take_iff_getElem.mp scheduled
  let t : Fin (es).length:=⟨n,hn.trans_le (min_le_right ..)⟩
  have located : (es).get t=ev:=atDate
  exact eventRead t (hn.trans_le (min_le_left ..)) s (by rw [located];exact found) edge

/-- The previous paid stock in a later memory is the same earlier array.
Every new paid width in the current slab is charged exactly once, even
when several contributors choose the same physical edge. -/
theorem wire_paid_step (initial : Memory w) (bits : ℕ) (j : Fin (es).length)
    (old : ∀t : Fin (es).length,t.val < j.val→∀s∈v.wideEventSlices h width bits ((es).get t),
       ∀e : Fin rows,s.load (memAt initial j.val) e=s.load (chk initial) e)
    (new : ∀t : Fin (es).length,t.val < j.val+1→∀s∈v.wideEventSlices h width bits ((es).get t),
       ∀e : Fin rows,s.load (memAt initial (j.val+1)) e=s.load (chk initial) e) (e : Fin rows) :
    v.wirePaidAt h width bits (j.val+1) (memAt initial (j.val+1)) e=
      v.wirePaidAt h width bits j.val (memAt initial j.val) e+
      PaidWidths.total (v.wideEventSlices h width bits ((es).get j)) (memAt initial (j.val+1)) e := by
  have before:=v.wire_paid_preserved_of_events h width initial bits j.val j.isLt.le old e
  have next:=v.wire_paid_preserved_of_events h width initial bits (j.val+1) j.isLt new e
  have now:=PaidWidths.total_rows_congr (v.wideEventSlices h width bits ((es).get j))
    (memAt initial (j.val+1)) (chk initial) (new j (Nat.lt_succ_self _)) e
  rw [next,before,now,v.wire_paid_next]

/-- Read a true executed width prefix page through the original evolving
stock tape, for any native edge ordinal. -/
theorem wire_paid_page (initial out : Memory w) (bits : ℕ) (j : ℕ) (last : j≤(es).length)
    (rowsRead : ∀t : Fin (es).length,t.val < j→∀s∈v.wideEventSlices h width bits ((es).get t),
      ∀e : Fin rows,s.load (memAt initial j) e=s.load (chk initial) e)
    (e : Fin rows) (original :
      (out (((v.wideWidthLayout h width (v.widePaidSlices h width bits)).bank j).base+e.val)).val=
        PaidWidths.total (PrefixWidths.prefixRows es (v.wideEventSlices h width bits) j) (chk initial) e) :
    (out (((v.wideWidthLayout h width (v.widePaidSlices h width bits)).bank j).base+e.val)).val=
      v.wirePaidAt h width bits j (memAt initial j) e :=
  original.trans (v.wire_paid_preserved_of_events h width initial bits j last rowsRead e).symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

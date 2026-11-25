import OAI.Hierarchy.ProtocolRAMPaidCheckoutEvent
import OAI.Hierarchy.ProbeFixedWidePaidRun
import OAI.Hierarchy.ProbeFixedWideSpillCases
import OAI.Hierarchy.ProbeFixedBroadcastCap
import OAI.Hierarchy.ProbeCatalystPrefixKeys

namespace OAI
/-! # Income archives at elapsed dates and immutable early spill routes -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
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
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
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

theorem prior_paid_low (m : Memory w) (active : Calendar.mounted C es m) (t : Fin (es).length)
    (j : ℕ) (past : t.val < j) (last : j≤(es).length) :
    PrefixAgreement.Low (until ((es).get t)) (checkedOut C floor m) (StockBound.state C m j) := by
  intro x hx
  have retired := (A).within v.mesh ((es).get t) ((es).get_mem t)
  exact (CatalystArchive.prefix_word C A m floor active
    (fun e u hu=>(v.event_prefix P h width r banks (TerminalLayout.source page)
      (TerminalLayout.table page) (TerminalLayout.destination page) ownerBank e u hu).1)
    t j past last x hx (ne_of_lt (hx.trans_le retired))).symm

/-- The dyadic direct and broadcast lookup banks are fully inside the slab
of their own attempt. -/
theorem prior_amount_banks (a : Attempt) (live : Event.attempt a∈es) (word : floor<2^w) :
    let b:=(f a).pricedArea
    (PaidWidths.archivedBank b.direct b.occurrences).Fits w (until (.attempt a)) ∧
      (PaidWidths.archivedBank b.broadcast b.rows).Fits w (until (.attempt a)) := by
  intro b
  have goods : b.goods=PurchaseInventory.footprint h N k := by cases a <;> rfl
  have pos : 0 < b.goods := by rw [goods];unfold PurchaseInventory.footprint;positivity
  have endAt:=v.attempt_room P h width a
  have room:=((A).within v.mesh (.attempt a) live).trans_lt word
  obtain ⟨d₀,b₀⟩:=PaidAmount.direct_broadcast_ends b (v.paid_attempt_rows P h width a) pos
  exact ⟨PaidAmount.archived _ _ _ _ (d₀.trans endAt) room,
    PaidAmount.archived _ _ _ _ (b₀.trans endAt) room⟩

theorem prior_feed_end (b : Boundary) (c : CommodityColumn)
    (here : c∈(lay b).columns) : c.overflow+c.rows ≤ until (.feed b) := by
  change c∈(List.finRange (FeedLayout.lanes N k)).map ((lay b).column) at here
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp here
  have span:=Nat.mul_le_mul_right (2^h) (show i.val+1 ≤ FeedLayout.lanes N k from i.isLt)
  rw [Nat.add_mul,one_mul] at span
  have fullStock : FeedLayout.lanes N k*2^h=PurchaseInventory.footprint h N k:=rfl
  rw [fullStock] at span
  have packed:=v.feed_room P h width
  change (A).base v.mesh (.feed b)+PurchaseInventory.footprint h N k+i.val*2^h+2^h ≤
    (A).base v.mesh (.feed b)+(A).stride
  omega

theorem prior_spill_operands (ev : Event) (scheduled : ev∈es) (word : floor<2^w) :
    let bound:=until ev
    (∀a : Attempt, let t:=v.paidSpillPath P h width recipe route order a
      t.edge.Fits w bound ∧ t.sourceRow.Fits w bound) ∧
    ∀b : Boundary,∀l : Fin (FeedLayout.lanes N k),
      let t:=v.paidFeedPath P h width route lay b ((lay b).column l)
      t.edge.Fits w bound ∧ t.sourceRow.Fits w bound := by
  intro bound
  have first : (A).first ≤ bound := (Nat.le_add_right (A).first _).trans (Nat.le_add_right _ _)
  have room : bound < 2^w := ((A).within v.mesh ev scheduled).trans_lt word
  have oldEnd : (ownerBank).base+(ownerBank).size≤(A).first := (v.catalyst_static_end P h width A).le
  have space:=allocated_space start cnt r (P).catalogue.rows w (⟨0,page+2⟩ : Bank) (8*2^page) (oldEnd.trans_lt (first.trans_lt room))
  have b₀:=space.kindEnd
  have b₁:=space.modeEnd
  have b₂:=space.operandEnd
  have safe:=CoreRoute.source_safe v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
    w bound ((v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans first)) room
  have ownerFits : (ownerBank).base ≤ bound :=
    ((Nat.le_add_right _ _).trans oldEnd).trans first
  have before (b : Bank) (endAt : b.base+b.size≤(ownerBank).base) : b.Fits w bound := by
    have whole := endAt.trans ownerFits
    exact ⟨Nat.two_pow_pos _,((Nat.le_add_left _ _).trans whole).trans_lt room,whole⟩
  have fit : (recipe).kind.Fits w bound ∧ (recipe).mode.Fits w bound ∧ (recipe).operand.Fits w bound:=
    ⟨before _ (by omega),before _ (by omega),before _ b₂⟩
  exact ⟨fun _=> earlyFits recipe route order paidO paidP safe fit,
    fun b l=> lane_fits route (decodeLane (feedLane (lay b) ((lay b).column l))) paidO paidP safe⟩

theorem prior_spill_load (π : Equiv.Perm (Fin (2^h))) (left right : Memory w)
    (native : v.WideSpillSource h width π left)
    (a : Attempt) (live : Event.attempt a∈es)
    (low : PrefixAgreement.Low (until (.attempt a)) left right) (word : floor<2^w)
    (menu : Fintype.card (Actions N k)≤2^w) (goods : Fintype.card (Commodity (Fin (2^h)) N k)≤2^w)
    (edges : (P).catalogue.rows≤2^w) (e : Fin (P).catalogue.rows) :
    let ar:=(f a).pricedArea
    let t:=v.paidSpillPath P h width recipe route order a
    let s:=PaidWidths.paidSpill ar t.positions t.owner t.parity t.edge t.sourceRow
    s.load left e=s.load right e := by
  intro ar t s
  obtain ⟨facts,installed⟩:=native
  have id:=(v.prior_spill_operands h width (.attempt a) live word).1 a
  have read:=v.spill_read P h width π (v.wideOrder h width) left route facts recipe
    (fun z : Columns h D×Fin k=>(pairKeys (Columns h D) k z).val) installed menu goods edges paidO paidP a
  apply PaidWidths.load_congr
  · intro i
    exact PrefixAgreement.expr t.edge left right _ (PrefixAgreement.inputEnd_of_fits _ id.1) low _
  · intro i
    apply PaidWidths.lookup_congr_at _ _ _ t.sourceRow left right _ id.2 low
    · exact (read.ownerAt i).trans_lt (read.enum i).1.isLt
    · calc
        ar.output+ar.goods+ar.goods+ar.goods = ar.output+3*ar.goods := by omega
        _ ≤ until (.attempt a) := v.attempt_room P h width a

theorem prior_feed_load (π : Equiv.Perm (Fin (2^h))) (left right : Memory w)
    (native : v.WideSpillSource h width π left) (b : Boundary) (live : Event.feed b∈es)
    (low : PrefixAgreement.Low (until (.feed b)) left right) (word : floor<2^w)
    (edges : (P).catalogue.rows≤2^w)
    (lanes : ∀l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^h<2^w)
    (c : CommodityColumn) (hc : c∈(lay b).columns) (e : Fin (P).catalogue.rows) :
    let s:=c.paidSlice (v.paidFeedPath P h width route lay b c)
    s.load left e=s.load right e := by
  intro s
  have endAt:=v.prior_feed_end h width b c hc
  change c∈(List.finRange (FeedLayout.lanes N k)).map ((lay b).column) at hc
  obtain ⟨l,_,rfl⟩:=List.mem_map.mp hc
  have fit:=(v.prior_spill_operands h width (.feed b) live word).2 b l
  have read:=v.boundary_read P h π (v.wideOrder h width) left route native.1 (lay b) paidO paidP l (lanes l) edges
  exact PaidCheckout.feed ((lay b).column l) (v.paidFeedPath P h width route lay b ((lay b).column l))
    (until (.feed b)) left right low e fit endAt (fun i => (read.ownerAt i).trans_lt (read.enum i).1.isLt)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

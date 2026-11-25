import OAI.Hierarchy.ProbeFixedWideBallotFields
import OAI.Hierarchy.ProbeFixedPaidSlabCell
import OAI.Hierarchy.ProbeFixedFailureEconomy
import OAI.Hierarchy.ProtocolRAMCalendarPricedBallot
import OAI.Hierarchy.TaggedWireFixedAdmission
import OAI.Hierarchy.TaggedWireBranchRead
import OAI.Hierarchy.ProbeFixedWideBallotOperandFits

namespace OAI
/-! # Authenticated native site ballot at a completed dated memory -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart PurchaseStage RepairHistogram WireTelescope WideCPU
open scoped Classical Fin.CommRing BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (h width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "W" => wordBits h (2^v.W) copies
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "fs" => v.nativeFormats P h width
local notation "A" => v.privateArena P h width
local notation "slab" => v.slab (v.seed P h width) P width
local notation "B" => v.nativeBoards P h width
variable (siteROM : ℕ) (a : Attempt) (prior tail : List Event)
  (mem entry out : Memory (wordBits h (2^v.W) copies))
  (cut : Slot (v.nativeChart P h width r banks src tab dst owners) mem (.attempt a) prior tail entry)
  (archive : ∀x,x<(v.privateArena P h width).endAddress v.mesh →
    out x=checkedOut (v.nativeChart P h width r banks src tab dst owners)
      ((v.privateArena P h width).endAddress v.mesh) mem x)
local notation "L" => (C).layout a
local notation "b" => enabledBatch L (repair C a)
local notation "snap" => HistogramShelf.snapshot C a entry
local notation "fields" => v.wideFields P h width siteROM (.attempt a)

include cut archive

/-- The literal seventh word of the report is the actual committed menu choice,
even if the copy count vanishes. The original attempt supplies the word. -/
theorem wide_ballot_code (board : Board L (repair C a) W) (rowsFit : (L).candidates≤2^W)
    (party : Fin (v.wideBallotParties h a)) (i : Fin (L).candidates) :
    ((fields).selected party).eval out (i.val:Word W)=
      if committed b snap (i.val:Word W) then (b).packet.eval snap (i.val:Word W) else 0 := by
  let raw := repair C a
  let step : Pass := ⟨raw.reportOut 6,(L).candidates,raw.link.fields b raw.reportWidth 6⟩
  have member : step∈writes L raw := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨6,rfl⟩
  have number:=attempt_read C a entry cut.currentReady board step member i
  have audit : (inspection L raw).Fits W := cut.currentReady.2.2.2.2.2.2.1.1
  obtain ⟨_,_,_,letters,copiesFit,total⟩ := audit
  have before : raw.reportOut 6+i.val<(A).base v.mesh (.attempt a)+(A).stride :=
    (Nat.add_lt_add_left i.isLt _).trans_le ((fs a).chargeColumns.2.1.trans (v.attempt_room P h width a))
  have occurs : Event.attempt a∈events v.mesh := by change _∈events (C).mesh;rw [cut.events];simp
  change (Ballot.code (raw.reportOut 6) (L).candidates).eval out (i.val:Word W)=_
  rw [Ballot.code_read _ out i rowsFit,archive _ (before.trans_le ((A).within v.mesh _ occurs)),
    v.paid_slab_cell P h width r banks src tab dst owners (.attempt a) mem entry prior tail cut _ before]
  change after C (.attempt a) entry (raw.reportOut 6+i.val)=
    ((b).ifSelected ((b).ifPacket (b).packet (.lit 0)) (.lit 0)).eval snap (i.val:Word W) at number
  rw [number,(b).eval_ifSelected,(b).eval_ifPacket _ _ _ _ letters copiesFit total]
  by_cases live : (b).selected snap (i.val:Word W) <;> simp [committed,live,Expr.eval]

theorem wide_ballot_live (board : Board L (repair C a) W) (rowsFit : (L).candidates≤2^W)
    (p : Fin (v.wideBallotParties h a)) (i : Fin (L).candidates) :
    ((fields).selected p).eval out (i.val:Word W)≠0 ↔ committed b snap (i.val:Word W) := by
  rw [v.wide_ballot_code P h width r banks src tab dst owners siteROM a prior tail mem entry out cut archive board rowsFit p i]
  by_cases h : committed b snap (i.val:Word W)
  · simp [h,h.1.2.1]
  · simp [h]

/-- The finite header is the positive ordinal of the original menu entry
and the actual local party. This is the number selecting the installed packet. -/
theorem wide_ballot_tag (board : Board L (repair C a) W) (rowsFit : (L).candidates≤2^W)
    (p : Fin (v.wideBallotParties h a)) (i : Fin (L).candidates)
    (live : committed b snap (i.val:Word W))
    (atom : Fin (v.menuCodes (Stages h (2^v.W))))
    (same : ((b).packet.eval snap (i.val:Word W)).val=atom.val+1)
    (menuFit : 1+v.menuCodes (Stages h (2^v.W))≤2^W)
    (tagsFit : v.menuCodes (Stages h (2^v.W))*v.wideBallotParties h a+1≤2^W) :
    (((fields).value p (0 : Fin (sig+2))).eval out (i.val:Word W)).val=(finProdFinEquiv (atom,p)).val+1 := by
  apply Ballot.participant_index _ _ _ _ _ atom menuFit tagsFit
  have saved:=v.wide_ballot_code P h width r banks src tab dst owners siteROM a prior tail mem entry out
    cut archive board rowsFit p i
  rw [ite_eq_left live] at saved
  exact (congrArg Fin.val saved).trans same

omit cut archive in
theorem ballot_before : (repair C a).keys≤(repair C a).verdict := by
  change (fs a).maskStart+2^(fs a).indexBits ≤ PostLayout.column (fs a).maskStart (fs a).indexBits (fs a).market.rows _
  unfold PostLayout.column PostLayout.startColumns
  omega

omit cut archive in
/-- The stock transaction and the original inspection count the same candidates.
This includes a valid zero-copy ballot. -/
theorem wide_ballot_in_tape_iff (layout : StockBound.TrialLayout C a (fs a).pricedArea (fs a).stockSource
      (v.stamp P h width r banks src tab dst owners a) v.keepLimit width ((A).base v.mesh (.attempt a)))
    (ready : Calendar.ready C (.attempt a) entry)
    (plan : StockCommit.PortPlan (v.taskCommit P h width a) b (v.stage P h width r banks src tab dst owners a entry)
      (fs a).market.rows) (i : Fin (L).candidates) :
    i∈(v.selectedTape P h width r banks src tab dst owners a entry layout ready plan).selected ↔
      committed b snap (i.val:Word W) := by
  let f:=fs a
  let g:=v.stamp P h width r banks src tab dst owners a
  have before:=v.ballot_before P h width r banks src tab dst owners a
  have room:=layout.window.wide
  have same:=priced_liveRows L (repair C a) f.pricedArea f.stockSource g (prepared C a entry)
    ready.2.2.2.2.2.2.1 ready.2.2.2.2.2.2.2.1 (by omega) before (before.trans (Nat.le_succ _))
      layout.window.label
  change i∈StockCommit.liveRows b (StockCommit.stageInput f.pricedArea f.stockSource g
    (postOutput L (repair C a) (prepared C a entry))) (L).candidates ↔_
  rw [same]
  simp only [StockCommit.liveRows,Finset.mem_filter,Finset.mem_univ,true_and,HistogramShelf.snapshot]

omit cut archive in
/-- The authenticated discrepancy/stock packet at the committed interface still
reads the original recommendation word at the repair snapshot. -/
theorem wide_ballot_packet_at_stage (layout : StockBound.TrialLayout C a (fs a).pricedArea (fs a).stockSource
      (v.stamp P h width r banks src tab dst owners a) v.keepLimit width ((A).base v.mesh (.attempt a)))
    (ready : Calendar.ready C (.attempt a) entry) (i : Fin (L).candidates) :
    (b).packet.eval (v.stage P h width r banks src tab dst owners a entry) (i.val:Word W)=
      (b).packet.eval snap (i.val:Word W) := by
  let raw:=repair C a
  let g:=v.stamp P h width r banks src tab dst owners a
  let post:=postOutput L raw (prepared C a entry)
  let checks:=ready.2.2.2.2.2.2.1
  let order:=ready.2.2.2.2.2.2.2.1
  obtain ⟨limit,before,ps⟩:=layout.board.snapshot
  let quote : Pass:=⟨raw.quoteOut,(L).candidates,(b).packet⟩
  have good : (b).packet.Fits W limit := (ps quote (List.mem_cons_self ..)).1
  have endFlag:=v.ballot_before P h width r banks src tab dst owners a
  have past (u : Audit) (hu : u∈audits L raw) : limit≤u.low := by
    change u∈Audit.check (inspection L raw)::columns (writes L raw) at hu
    rcases List.mem_cons.mp hu with rfl|later
    · exact before
    · have hi:=order.1 u later
      change raw.tally+1<u.low at hi
      have plan : (inspection L raw).Fits W:=checks.1
      have low:=plan.2.1
      change raw.keys+(L).candidates≤raw.tally at low
      change limit≤raw.keys at before
      omega
  exact (StockCommit.stage_input (fs a).pricedArea (fs a).stockSource g post (b).packet (i.val:Word W)
    (ProtocolRAMGeneratedWrite.fits_mono _ (before.trans (endFlag.trans (Nat.le_succ _))) good) layout.window.label).trans
    (post_input L raw (prepared C a entry) (b).packet (i.val:Word W) limit checks good past (before.trans endFlag))

variable (fits : (v.privateArena P h width).endAddress v.mesh<2^(wordBits h (2^v.W) copies))
  (copiesFit : v.menu.copiesAt v.copyScale width<2^(wordBits h (2^v.W) copies))
local notation "D" => v.nativeSelector P h width r banks src tab dst owners fits copiesFit

omit cut archive in
private theorem ballot_shelf_bound (i : Fin ((L).candidates*sig)) :
    ((D).bank a).base+i.val<(A).base v.mesh (.attempt a)+(A).stride := by
  have less : i.val<(L).candidates*sig:=i.isLt
  have capacity := (D).fits a
  change (fs a).market.rows*sig≤Slab.selectorSpan B at capacity
  have span : Slab.selectorSpan B≤(A).stride := by
    change Slab.selectorSpan B≤Slab.stride slab B
    simp only [Slab.stride,PostLayout.column,PostLayout.startColumns,Slab.mask,Slab.flags,Slab.first,
      Nat.zero_add,Nat.add_assoc]
    exact Nat.le_add_right ..
  exact Nat.add_lt_add_left (less.trans_le (capacity.trans span)) _

omit cut archive in
theorem ballot_shelf_safe (i : Fin ((L).candidates*sig)) :
    protected C (((D).bank a).base+i.val) (.attempt a) :=
  Slab.current_protected slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width)
    P.catalogue banks src tab dst owners (v.original_selector_room P h width fits)
    (v.original_copy_room P h width r banks src tab dst owners copiesFit) a i

include fits copiesFit in
/-- Every histogram lane is read out of the precise private input word which the
original candidate read prior to the verdict, including all padded zero lanes. -/
theorem wide_ballot_counter (p : Fin (v.wideBallotParties h a)) (i : Fin (L).candidates) (j : Fin sig) :
    ((fields).value p j.succ.succ).eval out (i.val:Word W)=
      (((C).raw a).batch.field j).eval snap (i.val:Word W) := by
  let pos:=finProdFinEquiv (i,j)
  have before:=v.ballot_shelf_bound P h width r banks src tab dst owners a fits copiesFit pos
  have safe:=v.ballot_shelf_safe P h width r banks src tab dst owners a fits copiesFit pos
  have occurs : Event.attempt a∈events v.mesh := by change _∈events (C).mesh;rw [cut.events];simp
  change (((C).raw a).batch.field j).eval out (i.val:Word W)=_
  rw [(D).fields,HistogramShelf.read_field _ out i j ((D).fits a) ((D).room a),
    HistogramShelf.read_field _ snap i j ((D).fits a) ((D).room a)]
  change out (((D).bank a).base+pos.val)=snap (((D).bank a).base+pos.val)
  rw [archive _ (before.trans_le ((A).within v.mesh _ occurs)),
    v.paid_slab_cell P h width r banks src tab dst owners (.attempt a) mem entry prior tail cut _ before,
    after_frame C (.attempt a) entry _ cut.currentReady safe,
    HistogramShelf.snapshot_frame C a entry _ cut.currentReady safe]

theorem wide_ballot_chosen (p : Fin (v.wideBallotParties h a)) (i : Fin (L).candidates) (j : Fin sig)
    (x : Memory W) (pick : BallChoices ((D).format.letters a x) ((D).format.copies a x))
    (tape : ((D).format.slot (.attempt a)).word x pick=(D).format.windows.read (.attempt a) entry) :
    ((fields).value p j.succ.succ).eval out (i.val:Word W)=
      counterRows ((D).format.letters a x) ((D).format.copies a x) pick ((D).format.count a x) i j :=
  (v.wide_ballot_counter P h width r banks src tab dst owners siteROM a prior tail mem entry out cut archive
    fits copiesFit p i j).trans
    ((D).format.field_on_branch a x entry pick i j cut.currentReady
      (v.ballot_shelf_safe P h width r banks src tab dst owners a fits copiesFit) tape)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

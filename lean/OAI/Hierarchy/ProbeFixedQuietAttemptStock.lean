import OAI.Hierarchy.ProbeFixedFailureStock

namespace OAI
/-! # The actual paid calendar copies every stock word on an idle attempt -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockCommit
open PurchaseStage RepairHistogram
open ThreeFlat.RAM
open scoped Fin.CommRing Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners

/-- Every repair row is disabled in the actual seeded histogram snapshot. -/
theorem rows_off_of_ne (a : Attempt) (entry : Memory W) (run : ready C (.attempt a) entry)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a)))
    (quiet : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))≠2)
    (j : Fin (f a).market.rows) : ¬committed (b a) (input a entry) (j.val:Word W) := by
  let B:=repair C a
  let L:=(C).layout a
  let u:=prepared C a entry
  let post:=postOutput L B u
  let ar:=(f a).pricedArea
  let s:=(f a).stockSource
  have window:=layout.window
  obtain ⟨_,_,_,_,_,room,checks,_,_,_,_,_,_⟩:=run
  have masked : post (B.repairBits.base+j.val)=0 :=
    mask_off L B layout.space u checks window.wide quiet j
  have ij : j.val<L.candidates:=j.isLt
  have late := layout.padBefore
  have addr : B.repairBits.base+j.val<(g a).out:=by
    change B.repairBits.base+L.candidates≤(g a).out at late
    omega
  have cell : input a entry (B.repairBits.base+j.val)=0 :=
    (ar.seed_frame s _ _ (.inl (addr.trans_le window.label))).trans
      ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl addr)).trans masked)
  intro active
  have enabled:=active.1.1
  change B.repairBits.read (input a entry) (j.val:Word W)≠0 at enabled
  change B.repairBits.base+L.candidates<2^W at room
  rw [Bank.read,Fin.val_cast_of_lt (by omega : j.val<2^W),
      Nat.mod_eq_of_lt (ij.trans_le layout.padded)] at enabled
  exact enabled cell

theorem quiet_rows (a : Attempt) (entry : Memory W) (run : ready C (.attempt a) entry)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a)))
    (quiet : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))<2)
    (j : Fin (f a).market.rows) : ¬committed (b a) (input a entry) (j.val:Word W) :=
  v.rows_off_of_ne P z width r banks src tab dst owners a entry run layout (Nat.ne_of_lt quiet) j

/-- The completed segment copies the lower and saved words and records zero spill. -/
theorem quiet_receipt (a : Attempt) (entry : Memory W) (run : ready C (.attempt a) entry)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a)))
    (ports : PortPlan (st a) (b a) (input a entry) (f a).market.rows)
    (quiet : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))<2)
    (i : Fin (st a).goods) :
    let out:=after C (.attempt a) entry
    out ((st a).plan.activeOut+i.val)=input a entry ((st a).plan.bank.base+i.val) ∧
    out ((st a).plan.activeOut+(st a).goods+i.val)=input a entry ((st a).plan.reserve.base+i.val) ∧
    out ((st a).plan.activeOut+(st a).goods+(st a).goods+i.val)=0 := by
  let B:=repair C a
  let L:=(C).layout a
  let u:=prepared C a entry
  let snap:=postSnapshot L B u
  let post:=postOutput L B u
  let ar:=(f a).pricedArea
  let s:=(f a).stockSource
  have window:=layout.window
  obtain ⟨pad,first,fees,flags,tape,cap,out,last⟩:=ar.order
  have limit := window.room
  change ar.stop<2^W at limit
  have small : ar.direct<2^W:=by omega
  have reserve : s.reserve.base+ar.goods≤ar.start:=
    window.reserve.trans window.label
  have mounted:=v.entered P z width r banks src tab dst owners a entry run
  have check : AuditReady (audits L B) snap:=run.2.2.2.2.2.2.1
  let j : Fin L.candidates:=⟨0,layout.positive⟩
  let mode : Pass:=⟨B.modeOut,L.candidates,AttemptGate.mode B.policy⟩
  have printed:=post_read L B u check layout.board mode
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) j
  have eventWord : post ((C).modeAt a)=(AttemptGate.actual B.policy snap:Word W):=
    printed.trans (AttemptGate.mode_eval ..)
  have signal : (s.mode.eval (pricedTransfer ar s (g a) (b a) post) (i.val:Word W)).val<2 := by
    rw [window.mode,word_eval,pricedTransfer_prior ar s (g a) (b a) post window.room window.label _
      window.modeBefore,eventWord,Fin.val_cast_of_lt ((AttemptGate.actual_lt ..).trans_le window.wide)]
    exact quiet
  have idle (j : Fin (st a).occurrences) : delta (st a).columns (input a entry) j=0:=by
    have disabled:=v.quiet_rows P z width r banks src tab dst owners a entry run layout quiet (ports.enum.symm j).1
    obtain ⟨add,sub⟩:=ports.off j (by simpa [StockCommit.liveRows] using disabled)
    have plus : (st a).columns.credit.eval (input a entry) (j.val:Word W)=0:=Fin.ext add
    have minus : (st a).columns.charge.eval (input a entry) (j.val:Word W)=0:=Fin.ext sub
    simp [delta,plus,minus]
  apply (st a).copy_receipt (b a) (input a entry) i mounted
  · change ar.direct≤ar.broadcast; omega
  · exact s.credit.fits_of_inputEnd (layout.inputs.credit.trans (show ar.start≤ar.direct by omega)) small
  · exact s.charge.fits_of_inputEnd (layout.inputs.charge.trans (show ar.start≤ar.direct by omega)) small
  · change ar.start+ar.goods≤ar.direct ∧ s.reserve.base+ar.goods≤ar.direct; omega
  · change ar.start+ar.goods≤ar.src ∧ s.reserve.base+ar.goods≤ar.src; omega
  · change ar.start+ar.goods≤ar.clip ∧ s.reserve.base+ar.goods≤ar.clip; omega
  · exact window.wide
  · exact ⟨pad.le,window.capacity.2⟩
  · exact .inr reserve
  · exact idle
  · exact ⟨Nat.ne_of_lt signal,by
      change (s.mode.eval (pricedTransfer ar s (g a) (b a) post) (i.val:Word W)).val≠3
      omega⟩

/-- Direct RAM readback at both published banks. The right sides refer to the
original entry memory, before guard, frozen sampler, label stamping and seeding. -/
theorem quiet_words (a : Attempt) (entry : Memory W) (run : ready C (.attempt a) entry)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a)))
    (ports : PortPlan (st a) (b a) (input a entry) (f a).market.rows)
    (quiet : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))<2)
    (i : Fin (st a).goods) :
    let ar:=(f a).pricedArea
    let s:=(f a).stockSource
    let out:=after C (.attempt a) entry
    out (ar.output+i.val)=entry (s.old.base+i.val) ∧
      out (ar.output+ar.goods+i.val)=entry (s.reserve.base+i.val) ∧
      out (ar.output+ar.goods+ar.goods+i.val)=0 := by
  intro ar s out
  let posted:=postOutput ((C).layout a) (repair C a) (prepared C a entry)
  let stamped:=((g a).pass ar.occurrences).apply posted
  let cutoff:=(v.privateArena P z width).base v.mesh (.attempt a)
  have small : ar.goods≤2^W:=by
    have h:=layout.window.room
    change ar.output+3*ar.goods<2^W at h
    omega
  have low (base : ℕ) (bound : base+ar.goods≤cutoff) : posted (base+i.val)=entry (base+i.val) :=
    postOutput_prior C a entry _ run ((v.event_prefix P z width r banks src tab dst owners (.attempt a) _
      ((Nat.add_lt_add_left i.isLt base).trans_le bound)).1)
  have label (base : ℕ) (bound : base+ar.goods≤(g a).out) : stamped (base+i.val)=posted (base+i.val) :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ((Nat.add_lt_add_left i.isLt base).trans_le bound))
  have read:=v.quiet_receipt P z width r banks src tab dst owners a entry run layout ports quiet i
  have old : input a entry (ar.start+i.val)=entry (s.old.base+i.val) :=
    ((ar.seed_read s stamped i small layout.window.capacity.1).trans (label _ layout.window.old)).trans
      (low _ layout.oldLow)
  have prior : s.reserve.base+i.val<ar.start :=
    (Nat.add_lt_add_left i.isLt _).trans_le (layout.window.reserve.trans layout.window.label)
  have saved : input a entry (s.reserve.base+i.val)=entry (s.reserve.base+i.val) :=
    ((ar.seed_frame s stamped _ (.inl prior)).trans (label _ layout.window.reserve)).trans (low _ layout.savedLow)
  exact ⟨read.1.trans old,read.2.1.trans saved,read.2.2⟩

set_option maxHeartbeats 1200000 in
/-- All physical commodity coordinates in the billed account agree between the
entry and successor of an idle attempt, including every live catalyst direction. -/
theorem quiet_stock (a : Attempt) (entry : Memory W) (scheduled : Event.attempt a∈events v.mesh)
    (run : ready C (.attempt a) entry)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a)))
    (ports : PortPlan (st a) (b a) (input a entry) (f a).market.rows)
    (quiet : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))<2) :
    let states:=Succession v.mesh (.attempt a)
    ((A).read states.2 (after C (.attempt a) entry)).bits=((A).read states.1 entry).bits := by
  intro states
  obtain ⟨before,afterStock⟩:=v.repair_stock P z width r banks src tab dst owners a entry scheduled run layout
  let E:=v.nativeSlots P z width a
  funext i
  have keep:=v.quiet_receipt P z width r banks src tab dst owners a entry run layout ports quiet (E i)
  have source := congrFun (v.native_end P z width r banks src tab dst owners a entry)
    ((st a).plan.activeOut+(E i).val)
  have kept := congrArg (fun word : Word W => word.val) (source.trans keep.1)
  have eqn := ((afterStock (E i)).trans kept).trans (before (E i)).symm
  change ((A).read states.2 (after C (.attempt a) entry)).bits (E.symm (E i))=
    ((A).read states.1 entry).bits (E.symm (E i)) at eqn
  simpa only [Equiv.symm_apply_apply] using eqn

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI

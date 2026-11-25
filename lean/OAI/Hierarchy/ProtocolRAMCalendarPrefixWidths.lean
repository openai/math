import OAI.Hierarchy.ProtocolRAMPaidWidthReplay
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices

namespace OAI
/-! # Paid width of every chronological calendar prefix on a concrete native tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PrefixWidths
open Computability.VPVNP.BurstRAM PrivateRAM PaidWidths
open ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing

def prefixRows (es : List Event) (compile : Event→List Slice) (j : ℕ) : List Slice :=
  (es.take j).flatMap compile

/-- The actual sparse direct, catalyst-mate, broadcast, spill and boundary slices are
shared with the terminal paid reporter, in the original event order. -/
def calendarRows {z d k q goods r edges : ℕ} (mesh : Mesh)
    (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals)
    (maxBroadcastBits : ℕ) : ℕ→List Slice :=
  prefixRows (events mesh) (eventSlices format feeds sink idBase role ids tree core boundary maxBroadcastBits)

theorem complete_rows {z d k q goods r edges : ℕ} (mesh : Mesh)
    (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals) (maxBroadcastBits : ℕ) :
    calendarRows mesh format feeds sink idBase role ids tree core boundary maxBroadcastBits (events mesh).length =
      paidSlices mesh format feeds sink idBase role ids tree core boundary maxBroadcastBits := by
  simp [calendarRows,prefixRows,paidSlices]

variable {W edges : ℕ} (L : Layout edges) (es : List Event) (compile : Event→List Slice)

/-- The aperture at the next public date includes precisely the new event, with
all positive repeated traversals charged to their original physical edge. -/
theorem prefix_step (m : Memory W) (e : Fin edges) (j : Fin es.length) :
    PaidWidths.total (prefixRows es compile (j.val+1)) m e =
    PaidWidths.total (prefixRows es compile j.val) m e + PaidWidths.total (compile es[j.val]) m e := by
  unfold prefixRows
  rw [List.take_succ_eq_append_getElem j.isLt]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    PaidWidths.total, List.map_append, List.sum_append]

theorem read_step (m : Memory W) (r : Receipt L (prefixRows es compile) m es.length)
    (e : Fin edges) (j : Fin es.length) :
    let out := image L (prefixRows es compile) m es.length
    (out ((L.bank (j.val+1)).base+e.val)).val =
      (out ((L.bank j.val).base+e.val)).val+PaidWidths.total (compile es[j.val]) m e := by
  intro out
  rw [r.read (j.val+1) j.isLt e,r.read j.val j.isLt.le e,prefix_step]

theorem prefix_total_le (m : Memory W) (j : ℕ) (e : Fin edges) :
    PaidWidths.total (prefixRows es compile j) m e≤PaidWidths.total (es.flatMap compile) m e := by
  have whole : es.flatMap compile =
      prefixRows es compile j ++ (es.drop j).flatMap compile := by
    unfold prefixRows
    rw [←List.flatMap_append, List.take_append_drop]
  rw [whole]
  simp [PaidWidths.total]

/-- Reusing the terminal sum's no-overflow receipt suffices at every earlier date,
and its archive read footprint works for each truncated slice list. -/
theorem ready_of_full (m : Memory W)
    (extent : ∀ j≤es.length,(L.bank j).base+edges<2^W)
    (mounted : ∀ j≤es.length,PaidWidths.Mounted (L.bank j) edges L.scratch (prefixRows es compile j) m)
    (immutable : ∀s∈es.flatMap compile,Archived W L.archive s)
    (fits : ∀e : Fin edges,PaidWidths.total (es.flatMap compile) m e<2^W) :
    Ready L (prefixRows es compile) m es.length := by
  refine ⟨extent,mounted,?_,fun j _ e=>(prefix_total_le es compile m j e).trans_lt (fits e)⟩
  intro j _ s hs
  apply immutable
  obtain ⟨ev,member,hs⟩ := List.mem_flatMap.mp hs
  exact List.mem_flatMap.mpr ⟨ev,List.take_subset j es member,hs⟩

/-- Rebase the original native directory, once, onto every fresh page.
Its parity and occurrence fields stay literal and only the destination base
constant changes. Thus mounting each prefix follows from the genuine original
terminal mounting and the numerical room of the new shared scratch. -/
theorem ready_of_original (m : Memory W) (origin : Bank) (src maxRows : ℕ)
    (old : PaidWidths.Mounted origin edges src (es.flatMap compile) m)
    (arch : origin.base≤L.archive) (later : src≤L.scratch)
    (separate : ∀ j≤es.length,(L.bank j).base+edges<L.scratch)
    (limit : L.scratch+2*maxRows<2^W) (count : ∀s∈es.flatMap compile,s.count≤ maxRows)
    (fits : ∀e : Fin edges,PaidWidths.total (es.flatMap compile) m e<2^W) :
    Ready L (prefixRows es compile) m es.length := by
  refine ready_of_full L es compile m ?_ ?_ ?_ fits
  · intro j hj
    exact (separate j hj).trans (by omega)
  · intro j hj s hs
    obtain ⟨event,inTake,entry⟩ := List.mem_flatMap.mp hs
    have orig : s∈es.flatMap compile := List.mem_flatMap.mpr ⟨event,List.take_subset j es inTake,entry⟩
    obtain ⟨valid,dir⟩ := old s orig
    have large := arch.trans (L.archive_le j)
    have sameCode : (RepairHistogram.pair (s.columns (L.bank j) edges)).Fits W src =
        (RepairHistogram.pair (s.columns origin edges)).Fits W src := rfl
    have pairFit : (RepairHistogram.pair (s.columns (L.bank j) edges)).Fits W src := by
      rw [sameCode]
      exact valid.pair
    have nativePair := ProtocolRAMGeneratedWrite.fits_mono _ later pairFit
    have length := count s orig
    exact ⟨⟨separate j hj,by omega,nativePair,
      ProtocolRAMGeneratedWrite.fits_mono _ large valid.edge,
      ProtocolRAMGeneratedWrite.fits_mono _ large valid.amount,valid.owner.trans large,valid.parity.trans large⟩,
      ⟨dir.first,dir.second,dir.firstRow,dir.secondRow⟩⟩
  · intro s hs
    have valid := (old s hs).1
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ arch valid.edge,
      ProtocolRAMGeneratedWrite.fits_mono _ arch valid.amount,valid.owner.trans arch,valid.parity.trans arch⟩

/-- Append to an already linked native producer of the frozen paid-archive memory.
The returned code preserves each original archive cell and exposes all original date/edge pairs. -/
theorem after_archive (A : Procedure W) (m archive : Memory W) (ticks : ℕ)
    (ran : A.Exec m archive ticks) (ready : Ready L (prefixRows es compile) archive es.length) :
    let rows := prefixRows es compile
    let out := image L rows archive es.length
    (A.seq (program L rows W es.length)).Exec m out (ticks+time L rows es.length) ∧
      (∀ a<L.archive,out a=archive a) ∧
      ∀ j≤es.length,∀ e : Fin edges,(out ((L.bank j).base+e.val)).val=
        PaidWidths.total ((es.take j).flatMap compile) archive e := by
  intro rows out
  have h := replay L rows archive es.length ready
  exact ⟨Procedure.Exec.then ran h.ran,h.kept,h.read⟩

private theorem charge_take {A B : Type*} (compile : A→List B) (charge : B→ℕ) (bound : ℕ)
    (es : List A) (j : ℕ) (maximal : ∀ e∈es,((compile e).map charge).sum≤bound) :
    (((es.take j).flatMap compile).map charge).sum≤j*bound := by
  induction j generalizing es with
  | zero => simp
  | succ j ih =>
    cases es with
    | nil => simp
    | cons e rest =>
      have tail := ih rest (fun t ht=>maximal t (List.mem_cons_of_mem _ ht))
      simpa only [List.take_succ_cons,List.flatMap_cons,List.map_append,List.sum_append,Nat.succ_mul,
        Nat.add_comm (j*bound) bound] using Nat.add_le_add (maximal e (by simp)) tail

/-- Price the literal seed and sparse scan at each date; each public event occurs
in at most the number of later slots. The public time polynomial has degree two. -/
theorem ticks_bound (perEvent : ℕ) (cap : ∀ j≤es.length,∀ ev∈es,
    ((compile ev).map (fun s=>RepairHistogram.ticks s.count (s.columns (L.bank j) edges))).sum≤perEvent) :
    time L (prefixRows es compile) es.length ≤
      (es.length+1)*(8+6*edges+es.length*perEvent) := by
  apply time_le
  intro j hj
  have small := charge_take compile (fun s=>RepairHistogram.ticks s.count (s.columns (L.bank j) edges))
    perEvent es j (cap j hj)
  have padded := Nat.mul_le_mul_right perEvent hj
  unfold PaidWidths.clock PaidWidths.scanTime prefixRows
  omega

theorem text_sum (rows : ℕ→List Slice) (n : ℕ) :
    text (program L rows W n)=∑ j : Fin (n+1), (30+
      ((rows j.val).map (fun s=>rowText (RepairHistogram.pair (s.columns (L.bank j.val) edges))+22)).sum) := by
  induction n with
  | zero => simpa [program,Fin.sum_univ_one] using paid_text W edges L.scratch (L.bank 0) (rows 0)
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,program,text_seq,ih,paid_text]; rfl

theorem text_bound (perEvent : ℕ) (cap : ∀ j≤es.length,∀ ev∈es,
    ((compile ev).map (fun s=>rowText (RepairHistogram.pair (s.columns (L.bank j) edges))+22)).sum≤perEvent) :
    text (program L (prefixRows es compile) W es.length)≤
      (es.length+1)*(30+es.length*perEvent) := by
  rw [text_sum]
  calc
    _ ≤ ∑ _ : Fin (es.length+1), (30+es.length*perEvent) := by
      apply Finset.sum_le_sum
      intro j _
      apply Nat.add_le_add_left
      exact (charge_take compile _ perEvent es j.val (cap j.val (by omega))).trans
        (Nat.mul_le_mul_right perEvent (by omega))
    _ = _ := by simp [Finset.sum_const]

end Hierarchy.ProtocolRAM.Calendar.PrefixWidths

end
end OAI

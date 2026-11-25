import OAI.Computability.BorderVNP.CellPacketSupplementalBatchTyped
import OAI.Computability.BorderVNP.RoutingISATypedBatchEntry

/-! # The consecutive supplemental and typed argument scans in the signed cell evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement.Batch

open VPVNP.BurstRAM CellSparse CellSparse.Packet

/-- The physical placement and measured private records of one owned generator cell. -/
structure Owned (Site : Type) where
  /-- Actual sparse packet with original boxes, ordinary rows, reports and external wires. -/
  placed : Placed Site
  /-- The four supplemental controls and the reserved tail position. -/
  layout : Layout
  /-- Beginning of the ordinary geometry record array. -/
  geometry : ℕ
  /-- Supplemental records emitted from private original site descriptions. -/
  extra : List Record
  /-- Owner column of the subsequent call row. -/
  callRow : ℕ

/-- The quantities compared with the actual runtime sidecar counters. -/
def Owned.cell {Site : Type} (o : Owned Site) : Cell :=
  ⟨o.layout,measured o.geometry o.placed.rows o.extra⟩

/-- Actual typed argument of this cell, with four tail descriptors in the order
emitted by the supplemental prepass. -/
def Owned.typed {Site : Type} (o : Owned Site) : TypedBatch.Task :=
  ⟨Supplement.task o.layout o.placed o.geometry o.extra,o.callRow⟩

variable {Site : Type} {w tasks controls count : ℕ}

/-- Physical data from the task and control table producers, public geometry, private
sidecar scan and boundary delivery. The record count of the public geometry is read
from the first word of its existing array. -/
structure Initial (o : Owned Site) (tasks controls i : ℕ) (m : Memory w) : Prop where
  taskRow : o.typed.Stored m tasks i
  controlRow : WordsAt (readings m) (controls+4*i) [o.layout.supplement,o.layout.counters,o.layout.merged,o.layout.reportWords]
  tailBase : readings m (o.layout.tail+1) = o.geometry
  tailLength : readings m (o.layout.tail+2) = 1+(o.placed.rows.flatMap record).length+o.layout.reportWords
  privateCount : readings m o.layout.counters = o.extra.length
  privateWords : readings m (o.layout.counters+1) = (o.extra.flatMap record).length
  report : o.layout.reportWords = (fieldList vector o.placed.reports).length
  prefixEnd : o.placed.descriptorBase+(CellPacket.descriptors (prefixChunks o.placed)).length = o.layout.tail
  original : Original o.placed o.layout o.geometry o.extra m
  mergeRoom : Room o.cell w
  typedRoom : o.typed.callRow+2 < 2^w ∧ o.typed.cell.Room w
  separateCount : o.layout.merged < o.layout.tail ∨ o.layout.tail+12 ≤ o.layout.merged

/-- Decode all ten initial supplemental reads from the two actual table rows and
the original producer arrays. The exclusive descriptor endpoint follows from the
seven-word row and the known number of trailing descriptors. -/
theorem Initial.stored {m : Memory w} {o : Owned Site} {i : ℕ} (h : Initial o tasks controls i m) :
    Stored o.cell tasks controls i m := by
  have geom := h.original.geom ⟨0,by simp [fieldList]⟩
  refine ⟨tailEnd_of_taskRow m o.placed o.layout o.geometry o.callRow o.extra h.prefixEnd h.taskRow,
    h.controlRow ⟨0,by simp⟩,h.controlRow ⟨1,by simp⟩,h.controlRow ⟨2,by simp⟩,
    h.controlRow ⟨3,by simp⟩,h.tailBase,h.tailLength,?_,h.privateCount,h.privateWords⟩
  simpa [fieldList,Owned.cell,measured] using geom

/-- Address protection for the two successive scans. The physical task and scalar
frame words must survive the supplemental descriptor patches. The typed batch then
uses its own chronological source and output separation. -/
structure Allocation (frame tasks controls count w : ℕ) (owned : ℕ → Owned Site) : Prop where
  scanReads : ∀ j < count, ∀ k < j, ∀ a ∈ (owned j).cell.sources tasks controls j, (owned k).cell.Outside a
  originals : ∀ i < count, ∀ k ≤ i, ∀ a, originalSource (owned i).placed (owned i).layout
    (owned i).geometry (owned i).extra a → (owned k).cell.Outside a
  patched : ∀ i < count, ∀ k, i < k → k < count → ∀ a,
    (owned i).typed.SourceAt tasks i a → (owned k).cell.Outside a
  taskRows : ∀ i < count, ∀ k < count, ∀ j < 7, (owned k).cell.Outside (tasks+7*i+j)
  frameWords : ∀ k < count, ∀ j ∈ [30,89,90], (owned k).cell.Outside (frame+j)
  typed : TypedBatch.Allocated w tasks count (fun i => (owned i).typed)

/-- The two consecutive native entries used by the real signed evaluator. -/
def prepareArguments : Code := .seq entry TypedBatch.entry

set_option maxRecDepth 3500 in
/-- First patch only the owned cells using their private counts, then run the real
typed initializer on all patched chunks and publish both argument fields in each call
row. Both stages share one memory and the ordinary evaluator frame. -/
theorem prepareArguments_run {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (s : Bank w) (m : Memory w) (owned : ℕ → Owned Site)
    (frame : (pub 0).val+92 < 2^w) (pointer : readings m ((pub 0).val+92)+11 < 2^w)
    (width : readings m ((pub 0).val+30) = w) (len : readings m ((pub 0).val+90) = count)
    (base : readings m ((pub 0).val+89) = tasks) (ctrl : readings m (readings m ((pub 0).val+92)+11) = controls)
    (taskFit : tasks+7*count ≤ 2^w) (controlFit : controls+4*count ≤ 2^w)
    (init : ∀ i < count, Initial (owned i) tasks controls i m)
    (alloc : Allocation (pub 0).val tasks controls count w owned) :
    let cells := fun i => (owned i).cell
    let rows := fun i => (owned i).typed
    let patched := written m cells count
    ∃ es t, Runs pub mac prepareArguments s m es t (TypedBatch.written patched rows count) ∧
      traceCost es ≤ 17+62*count+TypedBatch.loadDirectory.slots+TypedBatch.setup.slots+
        (∑ j ∈ Finset.range count, TypedBatch.rowCharge (fun k => (rows k).cell.cost w) j)+1 ∧
      (∀ event ∈ es, event.choices = [] ∧ event.sign = .plus) ∧ TypedBatch.Ready tasks count count t := by
  intro cells rows patched
  obtain ⟨xs,u,merge,b₁,_,_⟩ := entry_run (pub := pub) (mac := mac) s m cells frame pointer len base ctrl
    taskFit controlFit (fun i hi => ⟨(init i hi).stored,(init i hi).mergeRoom⟩) alloc.scanReads
  have kept (j : ℕ) (hj : j ∈ [30,89,90]) : patched ((pub 0).val+j) = m ((pub 0).val+j) :=
    preserve m cells (i := 0) (Nat.zero_le _) _ (fun k _ hk => alloc.frameWords k hk j hj)
  have source (i : ℕ) (hi : i < count) : (rows i).Stored patched tasks i ∧ (rows i).cell.Stored patched := by
    have h := init i hi
    exact ⟨task_row m cells _ h.taskRow (alloc.taskRows i hi),
      typed_stored m cells hi (owned i).placed (owned i).geometry (owned i).callRow (owned i).extra rfl
        h.report h.prefixEnd h.stored h.mergeRoom h.original h.separateCount (alloc.originals i hi) (alloc.patched i hi)⟩
  obtain ⟨ys,t,initRun,b₂,done⟩ := TypedBatch.entry_run pub mac u patched rows (by omega)
    ((congrArg Fin.val (kept 30 (by decide))).trans width) ((congrArg Fin.val (kept 89 (by decide))).trans base)
    ((congrArg Fin.val (kept 90 (by decide))).trans len) taskFit alloc.typed source (fun i hi => (init i hi).typedRoom)
  have full := merge.seq initRun
  refine ⟨_,t,full,?_,full.unsigned_events (by decide),done⟩
  rw [show traceCost (xs++ys) = traceCost xs+traceCost ys from VPVNP.RAMBuckets.cost_append ..]
  omega

end RoutingISA.CellPacket.Supplement.Batch

end BorderVNP
end Computability
end OAI

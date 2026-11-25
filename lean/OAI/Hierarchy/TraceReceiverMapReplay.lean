import OAI.Hierarchy.TraceReceiverMapForward
import OAI.Hierarchy.TraceReceiverFramedRoot

namespace OAI
/-! # Chronological replay from the genuine selected records and physical cache -/
noncomputable section
namespace Hierarchy.TraceReceiverForward
open ThreeFlat Diagonal RAM PhysicalStage HistoryContraction
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan
open RAM.TickTerminalRoot RAM.HistoryTerminalTape HistoryStageBody.Physical
open scoped Classical Fin.CommRing BigOperators

variable {F Pins : Type} [Field F] [Fintype F] {w u p suffix n d l : ℕ}

/-- Fixed data before the first root. The only physical observations indexed
by a root are published records, the original cache, and the real task entry. -/
structure Source (F Pins : Type) [Field F] [Fintype F] (w u p suffix n d l : ℕ) where
  initial : Memory (64*w)
  scan : Memory (64*w)
  x : TerminalWireArchive.Layout
  X : State d l
  L : X.Words Pins
  O : X.ArchiveSites
  order : X.OrderedHalves L
  site : Fin n → X.Site
  value : Fin n → NodeValue F
  tag : ((Fin 3→Bool)→F)→ℕ
  banks : NavigationNodeRows.Banks
  seeds : ℕ
  heapLo : ℕ
  heapHi : ℕ
  large : 7≤w
  age : u^10≤5*w
  jobs : 5*n≤GridReceiverBanks.gap w
  pinSum : (∑ i,L.ports.form.width (site i))≤GridReceiverBanks.gap w
  rowFit : (∑ i,(value i).net.cells)<2^(64*w)
  bitFit : (∑ i,(value i).net.internal)<2^(64*w)
  original : ∀ i,TraceReceiverRootRetain.Publication u (GridReceiverBanks.base w) p suffix seeds heapLo heapHi
    initial scan X L O (site i) (value i) tag banks x i (fun j=>(value j).net.cells)
  counts : initial (TickWorkspace.base u 18)=0 ∧ initial (TickWorkspace.base u 18+1)=(n:Word (64*w)) ∧
    initial (TickWorkspace.base u 18+2)=0 ∧ initial (TickWorkspace.base u 18+3)=0 ∧
    initial (TickWorkspace.base u 18+4)=(n:Word (64*w))
  task : ∀ i : Fin n,
    let D:=GridReceiverBanks.tasks w
    HistoryCommandTable.readTask initial ((D.tasks+5*i.val:ℕ):Word (64*w))=
      ⟨((TickWorkspace.base u 13+8*O.id (site i):ℕ):Word (64*w)),D.parent,
        ((D.maps+Tree.before (fun j=>L.ports.form.width (site j)) i:ℕ):Word (64*w)),
        (Tree.before (fun j=>(value j).net.cells) i:Word (64*w)),
        (Tree.before (fun j=>(value j).net.internal) i:Word (64*w))⟩

variable (P : Source F Pins w u p suffix n d l)

def Source.arena := mounted u p (2+suffix) P.x.prefixBase
def Source.rows (i : Fin n) := (P.value i).net.cells
def Source.bits (i : Fin n) := (P.value i).net.internal
def Source.ports (i : Fin n) := P.L.ports.form.width (P.site i)
def Source.dst (i : ℕ) := (GridReceiverBanks.tasks w).maps+scanned P.ports i
def Source.len (i : ℕ) := extent P.ports i
def Source.images (i : ℕ) := TraceReceiverTasks.mapImages P.arena (GridReceiverBanks.tasks w).tasks
  (GridReceiverBanks.mapHeader w) P.dst P.len P.initial i
def Source.seeded (i : ℕ) := TraceReceiverTasks.mapSeed P.arena (GridReceiverBanks.tasks w).tasks
  (GridReceiverBanks.mapHeader w) (P.images i)

structure Source.Invariant (i : ℕ) : Prop where
  controls : Controls u n P.rows P.bits i (P.images i)
  same : Reached u (GridReceiverBanks.base w) (GridReceiverBanks.tasks w).tasks n P.initial (P.images i)

include P in
theorem Source.page : TickWorkspace.base u 18+TickWorkspace.stride u < 2^(64*w) := by
  obtain ⟨bank,roof,space⟩:=TraceFactorReceiver.Gather.grid_window P.large P.age
  exact (TickWorkspace.apart (u:=u) (by decide : 18<45)).trans_lt (bank.trans (by omega))

include P in
theorem Source.countFits : n<2^(64*w) := by
  obtain ⟨bank,roof,space⟩:=TraceFactorReceiver.Gather.grid_window P.large P.age
  have hj := P.jobs
  omega

private theorem Source.seeded_agrees (i : ℕ) (h : P.Invariant i) :
    TraceReceiverRootRetain.Frame u (GridReceiverBanks.base w) P.initial (P.seeded i) := by
  intro a band
  have inRange : Stable u (GridReceiverBanks.base w) (GridReceiverBanks.tasks w).tasks n a := Or.inl band
  exact (seeded_frame (p:=p) (suffix:=suffix) (wire:=P.x.prefixBase) P.large P.age P.jobs
    (P.images i) a inRange).trans (h.same a inRange)

private theorem Source.receipt (i : Fin n) (h : P.Invariant i.val) :
    RootBounds P.arena (P.seeded i.val) ∧
      TraceReceiverTerminalMap.HalfRows P.X P.L (P.site i) (terminal P.arena (natMemory (P.seeded i.val)))
        (natMemory (P.seeded i.val)) suffix ∧
      CompactRootAt u p (2+suffix) P.x.prefixBase (P.seeded i.val) ∧
      (P.value i).Cached P.tag u (P.O.id (P.site i)) (P.seeded i.val) := by
  have cr (j : Fin 4) : P.seeded i.val (P.arena.control+j.val)=P.images i.val (P.arena.control+j.val) :=
    seeded_control P.large P.age (P.images i.val) j
  exact TraceReceiverRootRetain.selected_of_frame P.order (P.original i) (P.seeded_agrees i.val h)
    ((congrArg Fin.val (cr 0)).trans h.controls.ordinal)
    ((congrArg Fin.val (cr 2)).trans (h.controls.rowsRead.trans (scanned_at P.rows i)))

theorem Source.index (i : Fin n) (h : P.Invariant i.val) :
    rootId P.arena (natMemory (P.seeded i.val))=P.O.id (P.site i) := by
  let pub:=P.original i
  let fr:=P.seeded_agrees i.val h
  have cr : P.seeded i.val P.arena.control=P.images i.val P.arena.control :=
    seeded_control P.large P.age (P.images i.val) (0:Fin 4)
  have wide:= (TraceReceiverRootRetain.slot_room pub.large).1
  have vi:=pub.count
  exact TraceReceiverRootBounds.root_id (P.seeded i.val)
    ((congrArg Fin.val cr).trans h.controls.ordinal)
    (TraceReceiverRootRetain.pick fr (i:=i.val) (by have := i.isLt;omega) pub.picked)
    (TraceReceiverRootRetain.first fr (by omega) pub.first)

theorem Source.invariant (i : ℕ) (le : i≤n) : P.Invariant i := by
  induction i with
  | zero =>
    obtain ⟨c0,c1,c2,c3,c4⟩:=P.counts
    refine ⟨⟨?_,?_,?_,?_⟩,fun _ _=>rfl⟩
    · exact (congrArg Fin.val c0).trans rfl
    · exact (congrArg Fin.val c1).trans (Fin.val_cast_of_lt P.countFits)
    · change (P.initial (TickWorkspace.base u 18+2)).val=scanned P.rows 0
      rw [c2]
      simp [scanned]
    · change (P.initial (TickWorkspace.base u 18+3)).val=scanned P.bits 0
      rw [c3]
      simp [scanned]
  | succ k ih =>
    let i : Fin n:=⟨k,by omega⟩
    have h:=ih (by omega)
    obtain ⟨_,_,compact,cache⟩:=P.receipt i h
    have hd := cache.header
    have ix:=P.index i h
    let im:=P.images k
    have hsrc : HistoryStageRoot.atResult (natMemory (P.seeded k)) (P.arena.results+8*rootId P.arena (natMemory (P.seeded k)))=(P.value i).info := by
      rw [ix];exact hd
    have above : TickWorkspace.base u 18+4≤P.dst k := by
      obtain ⟨bank,roof,sp⟩:=TraceFactorReceiver.Gather.grid_window P.large P.age
      have h1:=TickWorkspace.apart (u:=u) (by decide : 18<45)
      change TickWorkspace.base u 18+4≤GridReceiverBanks.base w+2*GridReceiverBanks.gap w+_
      omega
    have next := controls_step (p:=p) (suffix:=suffix) (wire:=P.x.prefixBase) P.rows P.bits i (P.len k) (P.dst k)
      P.large P.age im h.controls P.countFits P.rowFit P.bitFit P.page above compact
      ⟨congrArg HistoryStageRoot.Result.rows hsrc,congrArg HistoryStageRoot.Result.bits hsrc⟩
    refine ⟨next,?_⟩
    intro a hAddr
    have untouched := step_frame P.large P.age P.jobs (P.dst k) (P.len k) (Nat.le_add_right ..) im P.page compact
    exact (untouched a hAddr).trans (h.same a hAddr)

/-- At any live iteration, the fixed original receipts recover that very
root's native bounds, actual numerical half rows, and selected physical cache. -/
theorem Source.iteration (i : Fin n) :
    RootBounds P.arena (P.seeded i.val) ∧
      TraceReceiverTerminalMap.HalfRows P.X P.L (P.site i) (terminal P.arena (natMemory (P.seeded i.val)))
        (natMemory (P.seeded i.val)) suffix ∧
      CompactRootAt u p (2+suffix) P.x.prefixBase (P.seeded i.val) ∧
      (P.value i).Cached P.tag u (P.O.id (P.site i)) (P.seeded i.val) :=
  P.receipt i (P.invariant i.val i.isLt.le)

end Hierarchy.TraceReceiverForward
end

end OAI

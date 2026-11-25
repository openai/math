import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.RAM.HistoryRootsCorrect
import OAI.ThreeFlat.RAM.CountedProcedure

namespace OAI
/-! # Native group, slot and terminal-ancestor publication in navigation -/

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.TickPhysicalABI RAM.TickGreedySweep
open RAM.TickGreedyNat RAM.HistoryNodeDirectory TickGreedyReplay LinearAlgebra.SpectralBooks.VNP
open scoped Fin.CommRing

variable {W n : ℕ} {α : Type*}

def ownerBase (a : RootArchive) := directory a.age 1
def chargeBase (a : RootArchive) := directory a.age 0
def descBase (a : RootArchive) := directory a.age 3
def statsBase (a : RootArchive) := TickWorkspace.base a.age 6

def partitionLayout (a : RootArchive) : TickGreedySetup.Layout :=
  ⟨a.chargeBase,a.ownerBase,a.statsBase+1,a.statsBase+2,a.groups,a.totalPairs,a.slotBudget⟩

structure PartitionRoom (a : RootArchive) (W : ℕ) : Prop where
  src : a.chargeBase+2*a.rootCount<2^W
  dst : a.ownerBase+2*a.rootCount<2^W
  forward : a.ownerBase≤a.chargeBase ∨ a.chargeBase+2*a.rootCount≤a.ownerBase
  stats : a.statsBase+2<2^W

def partitionInput (a : RootArchive) (total : ℕ) (items : List (Pair W)) (m : Memory W) :=
  m (a.statsBase+1)=(a.rootCount:Word W) ∧ m (a.statsBase+2)=(total:Word W) ∧ Stores m a.chargeBase items

def nativeOwners (a : RootArchive) (total : ℕ) (items : List (Pair W)) :=
  let gc:=4*(total*a.totalPairs)
  let sc:=a.slotBudget/4
  (replay (data a.groups total a.totalPairs gc sc) (encode ((0,gc),(0,sc))) items).2

/-- The actual S6 count and total drive the 48-label bank. This word-level
recurrence includes empty arrays and zero budgets. -/
theorem partition_replay_spec (a : RootArchive) (total : ℕ) (items : List (Pair W))
    (room : PartitionRoom a W) (size : items.length=a.rootCount) :
    (a.partition (W:=W)).Spec (a.partitionInput total items)
      (fun input out=>out=putPairs input a.ownerBase (a.nativeOwners total items)) (19+24*a.rootCount) := by
  intro p r k M pc R pub exit installed _ c m start facts
  obtain ⟨count,weight,stored⟩ := facts
  obtain ⟨out,run,atExit,_⟩ := TickGreedySetup.advance_replay a.partitionLayout total items M pc R pub exit
    installed (by change a.chargeBase+2*items.length<_; rw [size]; exact room.src)
    (by change a.ownerBase+2*items.length<_; rw [size]; exact room.dst)
    (by change a.ownerBase≤a.chargeBase ∨ a.chargeBase+2*items.length≤a.ownerBase; rw [size]; exact room.forward)
    c m start stored (by change a.statsBase+1<_; have := room.stats; omega) room.stats
    (by change m (a.statsBase+1)=_; simpa only [size] using count) weight
  exact ⟨19+24*items.length,by rw [size],out,_,run,atExit,rfl⟩

/-- Every item has a real positive work charge and fits the two physical cursors.
The final field says the requested number of slots suffices for each group. -/
structure ScheduleFacts (a : RootArchive) (W teams : ℕ) (work pairs : α→ℕ) (xs : List α) : Prop where
  groups : 0<a.groups
  nonempty : 0<Team.ticks work xs
  pairPositive : 0<a.totalPairs
  groupFit : 4*(Team.ticks work xs*a.totalPairs)<2^W
  slotFit : a.slotBudget/4<2^W
  positive : ∀ x∈xs, 0<work x
  pairBound : Team.ticks pairs xs≤a.totalPairs
  cell : ∀ x∈xs,cellScore a.groups (Team.ticks work xs) a.totalPairs work pairs x≤2*(Team.ticks work xs*a.totalPairs)
  workBound : ∀ x∈xs,work x≤a.slotBudget/4
  covered : ∀ b∈schedule a.groups (Team.ticks work xs) a.totalPairs work pairs xs,
    (Team.handoff work (a.slotBudget/4) teams b).2=[]

def scheduled (a : RootArchive) (teams : ℕ) (work pairs : α→ℕ) (xs : List α) : List (Pair W) :=
  planned teams a.slotBudget a.groups (Team.ticks work xs) a.totalPairs work pairs xs

theorem native_scheduled (a : RootArchive) (teams : ℕ) (work pairs : α→ℕ) (xs : List α)
    (h : ScheduleFacts a W teams work pairs xs) :
    a.nativeOwners (Team.ticks work xs) (xs.map (weights (w:=W) work pairs))=a.scheduled teams work pairs xs :=
  replay_planned h.groups h.nonempty h.pairPositive teams a.slotBudget work pairs xs h.groupFit h.slotFit
    h.positive le_rfl h.pairBound h.cell h.workBound h.covered

theorem scheduled_length (a : RootArchive) (teams : ℕ) (work pairs : α→ℕ) (xs : List α)
    (h : ScheduleFacts a W teams work pairs xs) : (a.scheduled (W:=W) teams work pairs xs).length=xs.length := by
  rw [← native_scheduled a teams work pairs xs h]
  simp [nativeOwners]

/-- The two words at directory 1 + 2i are the scheduled group and flattened slot
of the i-th input root. Other banks retain the input memory exactly. -/
theorem partition_spec (a : RootArchive) (teams : ℕ) (work pairs : α→ℕ) (xs : List α)
    (room : PartitionRoom a W) (size : xs.length=a.rootCount) (h : ScheduleFacts a W teams work pairs xs) :
    (a.partition (W:=W)).Spec (a.partitionInput (Team.ticks work xs) (xs.map (weights work pairs)))
      (fun input out=>out=putPairs input a.ownerBase (a.scheduled teams work pairs xs)) (19+24*a.rootCount) := by
  rw [←native_scheduled a teams work pairs xs h]
  exact a.partition_replay_spec (Team.ticks work xs) (xs.map (weights (w:=W) work pairs)) room
    (by simpa only [List.length_map] using size)

/-- Turn pointwise native charge rows into the scan's two-word array precondition. -/
theorem stores_of_rows (m : Memory W) (base : ℕ) (xs : List (Pair W))
    (read : ∀ i : Fin xs.length,m (base+2*i.val)=xs[i.val].1 ∧ m (base+2*i.val+1)=xs[i.val].2) :
    Stores m base xs := by
  induction xs generalizing base with
  | nil => trivial
  | cons x xs ih =>
    have first := read 0
    refine ⟨by simpa using first.1,by simpa using first.2,ih (base+2) ?_⟩
    intro i
    simpa only [Fin.val_succ,List.getElem_cons_succ,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,
      Nat.add_left_comm] using read i.succ

def ancestorBanks (a : RootArchive) : Reverse.Banks W := ⟨a.firstFinal,a.nodeBank.nodes,a.rootCache⟩

structure AncestorRoom (a : RootArchive) (W n : ℕ) : Prop where
  count : n<2^W
  desc : a.descBase+1<2^W
  stats : a.statsBase+1<2^W
  directory : a.nodeBank.nodes+8*n≤a.rootCache
  cache : a.rootCache+n≤2^W
  cacheBase : a.rootCache<2^W

def ancestorInput (a : RootArchive) (C : Chronology n) (m : Memory W) :=
  m a.descBase=(a.firstFinal:Word W) ∧ m (a.descBase+1)=(a.nodeBank.nodes:Word W) ∧
  m (a.statsBase+1)=(a.rootCount:Word W) ∧
  ∀ i : Fin n, i.val<a.firstFinal → m (a.nodeBank.nodes+8*i.val+1)=((C.parent i).val:Word W)

def ancestorPost (a : RootArchive) (C : Chronology n) (input out : Memory W) :=
  out=Reverse.sweep a.ancestorBanks n input ∧ (∀ i : Fin n,out (a.rootCache+i.val)=(C.root i:Word W)) ∧
    (∀ z,z<a.rootCache ∨ a.rootCache+n≤z → out z=input z)

/-- The reverse machine starts by reading the actual S11 root descriptor and S6
root count. Each earlier node inherits its parent's terminal ordinal. -/
theorem ancestors_spec (a : RootArchive) (C : Chronology n) (room : AncestorRoom a W n)
    (startAt : C.firstFinal=a.firstFinal) (total : a.firstFinal+a.rootCount=n) :
    (a.ancestors (W:=W)).Spec (a.ancestorInput C) (a.ancestorPost C) (12+11*n) := by
  intro p r k M pc R pub exit installed data c m entry inputs
  obtain ⟨first,ptr,count,parent⟩ := inputs
  have d0 : M.publicData (pub (0 : Fin 3))=(a.descBase:Word W) := data (0 : Fin 3)
  have d1 : M.publicData (pub (1 : Fin 3))=((a.statsBase+1:ℕ):Word W) := data (1 : Fin 3)
  have d2 : M.publicData (pub (2 : Fin 3))=(a.rootCache:Word W) := data (2 : Fin 3)
  have df := room.desc
  have af : a.descBase<2^W := by omega
  have nfit := room.count
  have ff : a.firstFinal<2^W := by omega
  have rf : a.rootCount<2^W := by omega
  have nf : a.nodeBank.nodes<2^W := (by have := room.directory; have := room.cacheBase; omega)
  have literal : ((a.descBase:Word W)+1).val=a.descBase+1 := by
    rw [←Nat.cast_add_one,Fin.val_cast_of_lt df]
  have banks : Reverse.banks (M.publicData∘pub) m=a.ancestorBanks := by
    change Reverse.Banks.mk (m (M.publicData (pub (0 : Fin 3))).val)
      (m (M.publicData (pub (0 : Fin 3))+1).val) (M.publicData (pub (2 : Fin 3))) =
      ⟨(a.firstFinal : Word W),(a.nodeBank.nodes : Word W),(a.rootCache : Word W)⟩
    rw [d0,d2,Fin.val_cast_of_lt af,literal,first,ptr]
  have actual : (m (M.publicData (pub (1 : Fin 3))).val).val+(m (M.publicData (pub (0 : Fin 3))).val).val=n := by
    rw [d0,d1,Fin.val_cast_of_lt af,Fin.val_cast_of_lt room.stats,first,count,Fin.val_cast_of_lt ff,
      Fin.val_cast_of_lt rf]
    omega
  obtain ⟨t,ht,rs,done⟩ := Reverse.run M pc R pub exit installed c m entry n actual room.count
  rw [banks] at done
  refine ⟨_,ht,_,_,done,rfl,rfl,?_,?_⟩
  · intro i
    have cor := Reverse.sweep_correct_of_inner C (a.ancestorBanks (W:=W)) m
      (by change (a.firstFinal:Word W).val=C.firstFinal; rw [Fin.val_cast_of_lt ff,startAt]) room.count
      (by simpa only [ancestorBanks,Fin.val_cast_of_lt nf,Fin.val_cast_of_lt room.cacheBase] using room.directory)
      (by simpa only [ancestorBanks,Fin.val_cast_of_lt room.cacheBase] using room.cache)
      (by simpa only [ancestorBanks,Fin.val_cast_of_lt nf,startAt] using parent) i
    simpa only [ancestorBanks,Fin.val_cast_of_lt room.cacheBase] using cor
  · intro z hz
    exact Reverse.sweep_frame (a.ancestorBanks (W:=W)) m n
      (by simpa only [ancestorBanks,Fin.val_cast_of_lt room.cacheBase] using room.cache) z
      (by simpa only [ancestorBanks,Fin.val_cast_of_lt room.cacheBase] using hz)


/-- The S11 owner writes miss the root header, S6 metadata and S44 parent array;
the S45 ancestor writes miss the S11 owner directory. -/
structure OwnerFrame (a : RootArchive) (n : ℕ) : Prop where
  desc : a.descBase+2≤a.ownerBase ∨ a.ownerBase+2*a.rootCount≤a.descBase
  count : a.statsBase+1<a.ownerBase ∨ a.ownerBase+2*a.rootCount≤a.statsBase+1
  parent : a.nodeBank.nodes+8*n≤a.ownerBase ∨ a.ownerBase+2*a.rootCount≤a.nodeBank.nodes
  cache : a.ownerBase+2*a.rootCount≤a.rootCache ∨ a.rootCache+n≤a.ownerBase

def ownersPost (a : RootArchive) (C : Chronology n) (labels : List (Pair W)) (input out : Memory W) :=
  out=Reverse.sweep a.ancestorBanks n (putPairs input a.ownerBase labels) ∧
  (∀ i : Fin labels.length,out (a.ownerBase+2*i.val)=labels[i.val].1 ∧
      out (a.ownerBase+2*i.val+1)=labels[i.val].2) ∧
  (∀ i : Fin n,out (a.rootCache+i.val)=(C.root i:Word W)) ∧
  (∀ z,(z<a.ownerBase ∨ a.ownerBase+2*a.rootCount≤z) → (z<a.rootCache ∨ a.rootCache+n≤z) → out z=input z)

private theorem preserve_ancestor_input (a : RootArchive) (C : Chronology n) (room : OwnerFrame a n)
    (labels : List (Pair W)) (size : labels.length=a.rootCount) (input : Memory W)
    (h : a.ancestorInput C input) : a.ancestorInput C (putPairs input a.ownerBase labels) := by
  obtain ⟨f,p,c,parents⟩ := h
  have frame (z : ℕ) (off : z<a.ownerBase ∨ a.ownerBase+2*a.rootCount≤z) :
      putPairs input a.ownerBase labels z=input z := putPairs_outside _ _ _ (by simpa only [size] using off)
  refine ⟨(frame _ (by have := room.desc; omega)).trans f,
    (frame _ (by have := room.desc; omega)).trans p,(frame _ room.count).trans c,?_⟩
  intro i earlier
  exact (frame _ (by have := room.parent; have := i.isLt; omega)).trans (parents i earlier)

private theorem owner_post (a : RootArchive) (C : Chronology n) (room : OwnerFrame a n) (labels : List (Pair W))
    (size : labels.length=a.rootCount) (input out : Memory W)
    (done : a.ancestorPost C (putPairs input a.ownerBase labels) out) : a.ownersPost C labels input out := by
  obtain ⟨eq,ancestor,keep⟩ := done
  refine ⟨eq,?_,ancestor,?_⟩
  · intro i
    have bounds := i.isLt
    have apart := room.cache
    rw [keep _ (by omega),keep _ (by omega)]
    exact stores_get _ _ _ (stores_putPairs input a.ownerBase labels) i
  · intro z o r
    exact (keep z r).trans (putPairs_outside input a.ownerBase labels (by simpa only [size] using o))

/-- Consecutive S11/S45 publication for arbitrary input charge words. The exact
two native memories and the frame are given also when the list of roots is empty. -/
theorem owners_replay_spec (a : RootArchive) (C : Chronology n) (items : List (Pair W)) (total : ℕ)
    (pr : PartitionRoom a W) (ar : AncestorRoom a W n) (frame : OwnerFrame a n)
    (size : items.length=a.rootCount) (startAt : C.firstFinal=a.firstFinal) (nodeCount : a.firstFinal+a.rootCount=n)
    (input : Memory W) (charges : a.partitionInput total items input) (links : a.ancestorInput C input) :
    ((a.partition (W:=W)).seq a.ancestors).Spec (·=input)
      (fun _ out=>a.ownersPost C (a.nativeOwners total items) input out) (19+24*a.rootCount+(12+11*n)) := by
  let labels:=a.nativeOwners total items
  have count : labels.length=a.rootCount := by simpa [labels,nativeOwners] using size
  let mid:=putPairs input a.ownerBase labels
  have left : (a.partition (W:=W)).Spec (·=input) (fun _ out=>out=mid) (19+24*a.rootCount) :=
    Procedure.Spec.atMemory (a.partition_replay_spec total items pr size) input charges
  have right : (a.ancestors (W:=W)).Spec (·=mid) (fun _ out=>a.ancestorPost C mid out) (12+11*n) :=
    Procedure.Spec.atMemory (a.ancestors_spec C ar startAt nodeCount) mid
      (preserve_ancestor_input a C frame labels count input links)
  intro p r k
  refine Procedure.Spec.mono (A := (a.partition (W:=W)).seq a.ancestors)
    (Procedure.Spec.seq (A := a.partition) (B := a.ancestors) left right (fun _ _ eqn => eqn))
    (fun _ h=>h) ?_ le_rfl
  rintro _ out ⟨_,_,done⟩
  exact owner_post a C frame labels count input out done

/-- Both native publication phases with the actual greedy root schedule. -/
theorem owners_spec (a : RootArchive) (C : Chronology n) (teams : ℕ) (work pairs : α→ℕ) (xs : List α)
    (pr : PartitionRoom a W) (ar : AncestorRoom a W n) (frame : OwnerFrame a n)
    (size : xs.length=a.rootCount) (startAt : C.firstFinal=a.firstFinal) (nodeCount : a.firstFinal+a.rootCount=n)
    (sched : ScheduleFacts a W teams work pairs xs) (input : Memory W)
    (charges : a.partitionInput (Team.ticks work xs) (xs.map (weights work pairs)) input)
    (links : a.ancestorInput C input) :
    ((a.partition (W:=W)).seq a.ancestors).Spec (·=input)
      (fun _ out=>a.ownersPost C (a.scheduled teams work pairs xs) input out) (19+24*a.rootCount+(12+11*n)) := by
  rw [← native_scheduled a teams work pairs xs sched]
  exact a.owners_replay_spec C (xs.map (weights (w:=W) work pairs)) (Team.ticks work xs) pr ar frame
    (by simpa only [List.length_map] using size) startAt nodeCount input charges links


end ThreeFlat.Diagonal.NavigationPass.RootArchive

end OAI

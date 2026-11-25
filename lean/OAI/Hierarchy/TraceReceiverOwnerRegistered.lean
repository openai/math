import OAI.Hierarchy.TraceReceiverOwnerRead
import OAI.Hierarchy.TraceReceiverOwnerParents
import OAI.Hierarchy.GridReceiverDirectoryFrame
import OAI.Hierarchy.FactorOccurrences

namespace OAI
/-! # The selected interpreter's owner mount from the actual T registration -/
namespace Hierarchy.TraceReceiverOwnerMount
open ThreeFlat RAM RAM.PhysicalProcedure RAM.HistoryNodeDirectory
open Diagonal Diagonal.HistoryContraction Diagonal.PhysicalStage Diagonal.TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section

/-- The resource classifier's outputs and the chronological parent table are
transported from their publishing instructions to the guard, with each dynamic
target read from the decoded T input. -/
theorem registered_after {F : Type} [Field F] {d l w u first n k T : ℕ} {X : State d l}
    (r : Run F X) (h : r.plan.History) (C : r.Charges) (O : X.ArchiveSites) (path : r.ArchivePath h C O)
    (b : NavigationNodeRows.Banks) (saved input assigned endState : Memory (64*w))
    (stored : r.ArchiveRowsStored b (fun a=>(saved a).val) h C O path) (zero : O.layer.first=0)
    (startAt : first=(r.finalArchive h C O path).1.first) (count : n=(r.finalArchive h C O path).1.count)
    (source : b.nodes=base u 44) (cache : ∀ a,base u 43 ≤ a → a < base u 45 → input a=saved a)
    (ht : 0 < T) (cost : Fin n → Fin k → ℕ) (tick : Fin T)
    (reg : GridSimulation.Assigned ht cost input assigned)
    (pub : GridReceiverTickDirectory.Ticked (GridReceiverTickDirectory.banks w u)
      (FactorAllocation.factors w cost (List.finRange n) tick) (tick.val:Word (64*w)) assigned endState)
    (pos : 0 < w) (upper : u^10 ≤ 5*w) (wide : 128 ≤ stride u)
    (old : 8*(first+n) ≤ stride u) (live : n ≤ GridPinArena.slab w)
    (mounted : Memory (64*w)) (keep : ∀ a, Reads u first n (GridReceiverTickDirectory.banks w u).owners
      ((GridReceiverTickDirectory.banks w u).scratch+1) a → mounted a=endState a) :
    let A:=GridReceiverTickDirectory.banks w u
    let chron:=r.archiveDirectory h C O path b (fun a=>(saved a).val) stored zero first n startAt count
    let D:=directory chron (fun j=>((FactorAllocation.owner ht w cost j).val:Word (64*w))) (tick.val:Word (64*w))
    let out:=output u first n A.owners (A.scratch+1) mounted
    (procedure (64*w) u first n A.owners (A.scratch+1)).Exec mounted out (ticks first n) ∧
    Selected.Recorded (data (64*w) u) D out ∧
    (out ((data (64*w) u) 4).val).val+(out ((data (64*w) u) 5).val).val=first+n ∧
    (∀ a,¬Touched u first n a → out a=mounted a) := by
  intro A chron D out
  let J:=GridDescription.sector w
  let g:=GridPinArena.slab w
  have word := GridPinArena.scales w pos
  change 32*g ≤ J ∧ 32*J < 2^(64*w) at word
  have scale : 64*stride u ≤ J:=sector pos upper
  have valid : 0 < g:=Nat.two_pow_pos _
  have gp : n ≤ g:=live
  have cap : Room (64*w) u first n A.owners (A.scratch+1) := by
    refine ⟨wide,old,?_,?_,?_⟩
    · change 47*stride u ≤ 15*J+3*g;omega
    · change 15*J+3*g+n ≤ 15*J+20*g+1;omega
    · change 15*J+20*g+1+1 < 2^(64*w);omega
  let ids:=FactorAllocation.factors w cost (List.finRange n) tick
  have listFits : ids.length ≤ n := by simpa using (FactorAllocation.factors_nodup ht w cost tick).length_le_card
  have scalar (j : Fin n) : endState (A.owners+j.val)=((FactorAllocation.owner ht w cost j).val:Word (64*w)) := by
    have hj:=j.isLt
    have frame:=pub.frame (A.owners+j.val) (.inr (by
      change 18*stride u+ids.length ≤ 15*J+3*g+j.val;omega)) (.inr (by
      change 19*stride u+5 ≤ 15*J+3*g+j.val;omega)) (.inl (by
      change 15*J+3*g+j.val < 15*J+20*g;omega))
    exact frame.trans (reg.owner j)
  have par:=HistorySelectedChildren.archive_parentAt r h C O path b saved stored zero first n startAt count
  have parent (i : Fin (first+n)) (earlier : i.val < chron.firstFinal) :
      endState (base u 44+8*i.val+1)=((chron.parent i).val:Word (64*w)) := by
    have hi:=i.isLt
    let x:=base u 44+8*i.val+1
    have eqn:=GridReceiverTickDirectory.outside_receiver ht cost tick reg pub x
      (by change 45*stride u+8*i.val+1 < 14*J;omega)
      (.inr (by change 18*stride u+ids.length ≤ 45*stride u+8*i.val+1;omega))
      (.inr (by change 19*stride u+5 ≤ 45*stride u+8*i.val+1;omega))
    have inCache := cache x (by change 44*stride u ≤ 45*stride u+8*i.val+1;omega)
      (by change 45*stride u+8*i.val+1 < 46*stride u;omega)
    exact eqn.trans (inCache.trans (by simpa only [source] using par i earlier))
  apply run cap chron rfl _ _ mounted
  · intro j
    have owned : A.owners ≤ A.owners+j.val ∧ A.owners+j.val < A.owners+n :=
      ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.isLt _⟩
    exact (keep (A.owners+j.val) (.inr (.inl owned))).trans (scalar j)
  · exact (keep _ (.inr (.inr rfl))).trans pub.targetAt
  · intro i hi
    have bound:=i.isLt
    exact (keep _ (.inl ⟨by omega,by omega⟩)).trans (parent i hi)

theorem registered {F : Type} [Field F] {d l w u first n k T : ℕ} {X : State d l}
    (r : Run F X) (h : r.plan.History) (C : r.Charges) (O : X.ArchiveSites) (path : r.ArchivePath h C O)
    (b : NavigationNodeRows.Banks) (saved input assigned endState : Memory (64*w))
    (stored : r.ArchiveRowsStored b (fun a=>(saved a).val) h C O path) (zero : O.layer.first=0)
    (startAt : first=(r.finalArchive h C O path).1.first) (count : n=(r.finalArchive h C O path).1.count)
    (source : b.nodes=base u 44) (cache : ∀ a,base u 43 ≤ a → a < base u 45 → input a=saved a)
    (ht : 0 < T) (cost : Fin n → Fin k → ℕ) (tick : Fin T)
    (reg : GridSimulation.Assigned ht cost input assigned)
    (pub : GridReceiverTickDirectory.Ticked (GridReceiverTickDirectory.banks w u)
      (FactorAllocation.factors w cost (List.finRange n) tick) (tick.val:Word (64*w)) assigned endState)
    (pos : 0 < w) (upper : u^10 ≤ 5*w) (wide : 128 ≤ stride u)
    (old : 8*(first+n) ≤ stride u) (live : n ≤ GridPinArena.slab w) :
    let A:=GridReceiverTickDirectory.banks w u
    let chron:=r.archiveDirectory h C O path b (fun a=>(saved a).val) stored zero first n startAt count
    let D:=directory chron (fun j=>((FactorAllocation.owner ht w cost j).val:Word (64*w))) (tick.val:Word (64*w))
    let out:=output u first n A.owners (A.scratch+1) endState
    (procedure (64*w) u first n A.owners (A.scratch+1)).Exec endState out (ticks first n) ∧
    Selected.Recorded (data (64*w) u) D out ∧
    (out ((data (64*w) u) 4).val).val+(out ((data (64*w) u) 5).val).val=first+n ∧
    (∀ a,¬Touched u first n a → out a=endState a) := by
  exact registered_after r h C O path b saved input assigned endState stored zero startAt count source cache
    ht cost tick reg pub pos upper wide old live endState (fun _ _=>rfl)

theorem picked_iff {W f n T : ℕ} (C : Chronology (f+n)) (first : C.firstFinal=f)
    (owner : Fin n → Fin T) (tick : Fin T) (i : Fin (f+n)) (small : f+n < 2^W) (fits : T ≤ 2^W) :
    Selected.picked (directory C (fun j=>((owner j).val:Word W)) (tick.val:Word W)) i.val=true ↔
      owner ⟨C.root i,by have:=C.root_lt i;rw [first] at this;omega⟩=tick := by
  have fit : C.root i < n:=by have:=C.root_lt i;rw [first] at this;omega
  let j : Fin n:=⟨C.root i,fit⟩
  have rr : (C.root i:Word W).val=C.root i:=Fin.val_cast_of_lt (by omega)
  simp only [Selected.picked,dite_eq_left i.isLt,decide_eq_true_eq,directory,rr,dite_eq_left fit]
  change ((0:Word W),((owner j).val:Word W))=((0:Word W),(tick.val:Word W)) ↔ owner j=tick
  constructor
  · intro eqn
    apply Fin.ext
    have h:=congrArg (fun z : Word W × Word W=>z.2.val) eqn
    simpa only [Fin.val_cast_of_lt ((owner j).isLt.trans_le fits),Fin.val_cast_of_lt (tick.isLt.trans_le fits)]
      using h
  · intro eqn;rw [eqn]

/-- A published parent chain from an actual initial lane selects the true terminal
tensor site of the same run. The guard therefore tests the native allocator ordinal
of its traced destination. -/
theorem picked_initial_iff {F : Type} [Field F] {d l W f n T : ℕ} {A : State d l}
    (r : Run F A) (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (b : NavigationNodeRows.Banks) (mem : ℕ → ℕ) (rows : r.ArchiveRowsStored b mem h C O p)
    (zero : O.layer.first=0) (first : f=(r.finalArchive h C O p).1.first)
    (count : n=(r.finalArchive h C O p).1.count) (owner : Fin n → Fin T) (tick : Fin T)
    (x : A.Site) (i : Fin (f+n)) (atSite : i.val=O.id x) (small : f+n < 2^W) (fits : T ≤ 2^W) :
    let D:=r.archiveDirectory h C O p b mem rows zero f n first count
    Selected.picked (directory D (fun j=>((owner j).val:Word W)) (tick.val:Word W)) i.val=true ↔
      owner (Fin.cast count.symm ((r.finalArchive h C O p).2 (r.rawDestination h x)))=tick := by
  intro D
  have terminal : D.root i=((r.finalArchive h C O p).2 (r.rawDestination h x)).val := by
    apply Run.root_of_archive D b mem _ r h C O p rows first x i atSite
    exact r.archiveDirectory_parent h C O p b mem rows zero f n first count
  rw [picked_iff D rfl owner tick i small fits]
  have id : (⟨D.root i,by have:=D.root_lt i;change D.root i<(f+n)-f at this;omega⟩ : Fin n)=
      Fin.cast count.symm ((r.finalArchive h C O p).2 (r.rawDestination h x)):=Fin.ext terminal
  rw [id]

end
end Hierarchy.TraceReceiverOwnerMount

end OAI

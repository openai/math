import OAI.Hierarchy.TraceReceiverTaskReads
import OAI.Hierarchy.TraceResourceMount
import OAI.ThreeFlat.Diagonal.HistoryPostorder
import OAI.Hierarchy.GridReceiverDirectoryROM

namespace OAI
/-! # S18 and the actual five-word tasks at the start of the terminal maps -/
noncomputable section
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat Diagonal.HistoryContraction RAM Computability.VPVNP.BurstRAM PrivateRAM
open HistoryCommandTable TraceAdmission.Resources
open scoped Fin.CommRing BigOperators Classical

variable {W N : ℕ}
variable (A : GridReceiverTickDirectory.Banks) (D : Layout) (ids : List (Fin N))
    (count cap : ℕ) (width : Fin 3→ℕ) (first : ℕ) (vals : Fin 3→Fin ids.length→ℕ)
    (prior elected : Memory W) (rootBase pins : ℕ)
set_option quotPrecheck false
local notation "m" => mounted D.parent [rootBase,pins,0,0] elected
local notation "after" => beforeImage D count cap width ids.length m
local notation "ord" => (fun j : Fin ids.length=>ids[j.val].val)
local notation "loc" => (fun j : Fin ids.length=>D.results+8*(first+ord j))

/-- The parent-header mount occurs before the prefix scans. All addresses
used to read S11, S13, S17 and S18 are explicitly below the temporary arena. -/
structure SelectedInputFacts : Prop where
  counters : after A.controls=0 ∧ after (A.controls+1)=(ids.length:Word W) ∧
    after (A.controls+2)=0 ∧ after (A.controls+3)=0 ∧ after (A.controls+4)=(ids.length:Word W)
  roster : ∀ i : Fin ids.length,after (D.selected+i.val)=(ord i:Word W)
  firstWord : after D.first=(first:Word W)
  frame : ∀ a<D.current,after a=elected a
  tasks : ∀ i : Fin ids.length,
    readTask after ((D.tasks+5*i.val:ℕ):Word W)=
      ⟨(loc i:Word W),D.parent,((D.maps+Tree.before (vals 0) i:ℕ):Word W),
        (Tree.before (vals 1) i:Word W),(Tree.before (vals 2) i:Word W)⟩
  totals : ∀ j,∑ i,vals j i≤cap
  num : m (A.controls+1)=(ids.length:Word W)
  caches : ∀ j (i : Fin ids.length),(amountAddress D.selected D.first D.results j m (i.val:Word W)).val<D.current


theorem before_selected (pub : GridReceiverTickDirectory.Published A ids prior elected)
    (selected : A.roots=D.selected) (ordWord : elected D.first=(first:Word W))
    (bounds : BeforeBounds D count cap width ids.length W)
    (apart : ColumnSeparation D width ids.length)
    (parent : D.current≤D.parent) (fit : D.parent+4≤2^W)
    (firstRoom : D.first<D.current) (rosterRoom : D.selected+ids.length≤D.current)
    (controlRoom : A.controls+4<D.current) (cacheRoom : ∀ i,loc i+4<D.current)
    (cached : ∀ i (j : Fin 3),(elected (loc i+(j.val+1))).val=vals j i)
    (small : ∀ j,∑ i,vals j i≤cap) :
    SelectedInputFacts A D ids count cap width first vals elected rootBase pins := by
  have ringRoom : D.current<2^W:=by omega
  have hp (a : ℕ) (ha : a<D.current) : m a=elected a :=
    mounted_frame D.parent _ elected (by simpa using fit) (.inl (by omega))
  have low (a : ℕ) (ha : a<D.current) : after a=elected a:=
    (before_low D count cap width ids.length bounds m a ha).trans (hp a ha)
  have src (i : Fin ids.length) : m (D.selected+i.val)=(ord i:Word W):=by
    rw [hp _ (by have:=i.isLt;omega),←selected]
    exact pub.roots i
  have fst : m D.first=(first:Word W):=(hp _ firstRoom).trans ordWord
  have addr (j : Fin 3) (i : Fin ids.length) :
      (amountAddress D.selected D.first D.results j m (i.val:Word W)).val=loc i+(j.val+1):=by
    dsimp only [amountAddress]
    rw [Fin.val_cast_of_lt (firstRoom.trans ringRoom),←Nat.cast_add,
      Fin.val_cast_of_lt (by have:=i.isLt;omega),src,fst]
    have e : (D.results:Word W)+8*((first:Word W)+(ord i:Word W))+((j.val+1:ℕ):Word W)=
        ((loc i+(j.val+1):ℕ):Word W):=by push_cast;ring
    rw [e,Fin.val_cast_of_lt (by have:=cacheRoom i;have:=j.isLt;omega)]
  have cache (j : Fin 3) (i : Fin ids.length) : cacheAmount D m j i.val=vals j i:=by
    rw [cacheAmount,addr,hp _ (by have:=cacheRoom i;have:=j.isLt;omega)]
    exact cached i j
  have sums (j : Fin 3) (i : Fin ids.length) :
      (∑ k : Fin i.val,cacheAmount D m j k.val)=Tree.before (vals j) i:=by
    apply Finset.sum_congr rfl
    intro k _
    exact cache j (Fin.castLE i.isLt.le k)
  refine ⟨?_,?_,(low _ firstRoom).trans ordWord,low,?_,small,(hp _ (by omega)).trans pub.controls.2.1,?_⟩
  · simpa only [low _ (by omega : A.controls<D.current),low _ (by omega : A.controls+1<D.current),
      low _ (by omega : A.controls+2<D.current),low _ (by omega : A.controls+3<D.current),
      low _ controlRoom] using pub.controls
  · intro i
    exact (before_low D count cap width ids.length bounds m _ (by have:=i.isLt;omega)).trans (src i)
  · intro i
    have t:=prepared_task D count cap width ids.length bounds apart m
      (fun j i=>by rw [addr];have:=cacheRoom i;have:=j.isLt;omega)
      (fun j=>by simpa only [cache] using small j) i
    dsimp only at t
    rw [fst,src i,sums 0 i,sums 1 i,sums 2 i] at t
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using t
  · intro j i
    rw [addr]
    have near:=cacheRoom i
    have hj:=j.isLt
    omega

end Hierarchy.TraceReceiverTasks
end

end OAI

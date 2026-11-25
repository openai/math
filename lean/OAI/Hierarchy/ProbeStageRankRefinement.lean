import OAI.Hierarchy.ProbeStageRankUpdate
import OAI.Hierarchy.ProbeStageScatterRefinement

namespace OAI
/-! # Actual per-endpoint ranks and first-saturation directory lengths -/

namespace Hierarchy.ProbeStage.RankUpdate
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- The physical chosen counter and the two immutable directory entries. -/
def counter {w : ℕ} (s : Layout) (m : Memory w) := m (s.counterBase:Word w).val + m (s.chosen:Word w).val

def dirWord {w : ℕ} (a chosen : ℕ) (m : Memory w) := m ((a:Word w)+m (chosen:Word w).val).val

/-- All six destinations in the actual setup, including the dynamically addressed counter. -/
def touched {w : ℕ} (s : Layout) (m : Memory w) := [s.ptr,s.rank,s.value,(counter s m).val,s.head,s.length]

def needed {w : ℕ} (s : Layout) (m : Memory w) := [(s.counterBase:Word w).val,(s.chosen:Word w).val,
    ((s.heads:Word w)+m (s.chosen:Word w).val).val,((s.lengths:Word w)+m (s.chosen:Word w).val).val]

structure Distinct {w : ℕ} (s : Layout) (m : Memory w) : Prop where
  nodup : (touched s m).Nodup
  fixed : ∀ x∈needed s m, ∀ y∈touched s m,x≠y
  fit : Fits w s

def newCount {w : ℕ} (s : Layout) (m : Memory w) := m (counter s m).val+1

def updates {w : ℕ} (s : Layout) (m : Memory w) : Memory w :=
  let a := Function.update m s.ptr (counter s m)
  let b := Function.update a s.rank (m (counter s m).val)
  let c := Function.update b s.value (newCount s m)
  let d := Function.update c (counter s m).val (newCount s m)
  let e := Function.update d s.head (dirWord s.heads s.chosen m)
  Function.update e s.length (if newCount s m=(s.quota:Word w) then dirWord s.lengths s.chosen m else 0)

private theorem put_eq {w : ℕ} (m : Memory w) (a v : Word w) : writeMemory m a v = Function.update m a.val v := by
  funext x
  by_cases h : x=a.val <;> simp [writeMemory,Function.update,h]

/-- The concrete five fixed-address writes and the indirect counter write have these exact
values. In particular the stored rank is the *previous* count on this side. -/
theorem prepared_eq {w : ℕ} (s : Layout) (m : Memory w) (sep : Distinct s m) :
    prepared s m=updates s m := by
  let addr := (counter s m).val
  let chosen := (s.chosen:Word w).val
  let head := ((s.heads:Word w)+m chosen).val
  let length := ((s.lengths:Word w)+m chosen).val
  have nd := sep.nodup
  change [s.ptr,s.rank,s.value,addr,s.head,s.length].Nodup at nd
  simp only [List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,List.nodup_nil,
    not_false_eq_true,and_true] at nd
  have fi (x) (h : x ∈ [(s.counterBase:Word w).val,chosen,head,length]) (y)
      (hy : y∈[s.ptr,s.rank,s.value,addr,s.head,s.length]) : x≠y := sep.fixed x h y hy
  have ptrFit : (s.ptr:Word w).val=s.ptr := Fin.val_cast_of_lt (by have := sep.fit.ptr;omega)
  have rankFit : (s.rank:Word w).val=s.rank := Fin.val_cast_of_lt (by have := sep.fit.rank;omega)
  have valFit : (s.value:Word w).val=s.value := Fin.val_cast_of_lt (by have := sep.fit.value;omega)
  let p := counter s m
  let v := newCount s m
  let a := Function.update m s.ptr p
  let b := Function.update a s.rank (m addr)
  let c := Function.update b s.value v
  let d := Function.update c addr v
  let e := Function.update d s.head (m head)
  have np : addr≠s.ptr := by tauto
  have pr : s.ptr≠s.rank := by tauto
  have pv : s.ptr≠s.value := by tauto
  have vh : s.value≠s.head := by tauto
  have va : s.value≠addr := by tauto
  have fr (x) (hx : x∈[chosen,head,length]) (y) (hy : y∈[s.ptr,s.rank,s.value,addr,s.head]) : x≠y := by
    apply fi x _ y _ <;> simp_all only [List.mem_cons] <;> tauto
  have readD (x) (hx : x∈[chosen,head,length]) : d x=m x := by
    simp only [d,c,b,a,Function.update_of_ne (fr x hx addr (by simp)),
      Function.update_of_ne (fr x hx s.value (by simp)),Function.update_of_ne (fr x hx s.rank (by simp)),
      Function.update_of_ne (fr x hx s.ptr (by simp))]
  have readE (x) (hx : x∈[chosen,head,length]) : e x=m x := by
    rw [show e x=d x from Function.update_of_ne (fr x hx s.head (by simp)) _ _,readD x hx]
  have getA : WordStore.value s.rank (getRank s) a=m addr := by
    change a (a (s.ptr:Word w).val).val=m addr
    rw [ptrFit,show a s.ptr=p from Function.update_self ..]
    exact Function.update_of_ne np _ _
  have getB : WordStore.value s.value (increment s) b=v := by
    change b (s.rank:Word w).val+1=v
    rw [rankFit,show b s.rank=m addr from Function.update_self ..];rfl
  have save : stored s.ptr s.value c=d := by
    change writeMemory c (c (s.ptr:Word w).val) (c (s.value:Word w).val)=d
    rw [ptrFit,valFit,show c s.value=v from Function.update_self ..,put_eq]
    have pp : c s.ptr=p := by simp only [c,b,a,Function.update_of_ne pv,Function.update_of_ne pr,Function.update_self]
    rw [pp]
  have readHead : WordStore.value s.head (directory s.heads s.chosen) d=m head := by
    change d ((s.heads:Word w)+d chosen).val=m head
    rw [readD chosen (by simp)]
    exact readD head (by simp)
  have readLength : WordStore.value s.length (activation s) e=(if v=(s.quota:Word w) then m length else 0) := by
    change (if decide (e (s.value:Word w).val=(s.quota:Word w))=true then e ((s.lengths:Word w)+e chosen).val else 0)=_
    have vv : e s.value=v := by simp only [e,d,c,Function.update_of_ne vh,Function.update_of_ne va,Function.update_self]
    rw [valFit,vv,readE chosen (by simp),show e ((s.lengths:Word w)+m chosen).val=m length from readE length (by simp)]
    simp
  change assign s.length (activation s) (assign s.head (directory s.heads s.chosen)
    (stored s.ptr s.value (assign s.value (increment s) (assign s.rank (getRank s) a))))=_
  rw [show assign s.rank (getRank s) a=b from congrArg (Function.update a s.rank) getA,
    show assign s.value (increment s) b=c from congrArg (Function.update b s.value) getB,save,
    show assign s.head (directory s.heads s.chosen) d=e from congrArg (Function.update d s.head) readHead]
  exact congrArg (Function.update e s.length) readLength

/-- True list length touched by the native scatter, including the zero length when the
quota is not attained on this record. -/
theorem occurrenceCount_spec {w : ℕ} (s : Layout) (m : Memory w) (sep : Distinct s m)
    (r : ℕ) (rank : (m (counter s m).val).val=r) (quotaFit : s.quota<2^w) (rankFit : r+1<2^w) :
    occurrenceCount s m = (if r+1=s.quota then (dirWord s.lengths s.chosen m).val else 0) := by
  have hz : m (counter s m).val=(r:Word w) := Fin.ext (by rw [Fin.val_cast_of_lt (by omega : r<2^w)];exact rank)
  have hc : newCount s m=(s.quota:Word w) ↔ r+1=s.quota := by
    rw [newCount,hz,← Nat.cast_one (R:=Word w),←Nat.cast_add,Fin.ext_iff,
      Fin.val_cast_of_lt rankFit,Fin.val_cast_of_lt quotaFit]
  simp only [occurrenceCount,prepared_eq _ _ sep,updates,Fin.val_cast_of_lt (by have := sep.fit.length;omega : s.length<2^w),
    Function.update_self,hc]
  split <;> rfl

theorem updates_elsewhere {w : ℕ} (s : Layout) (m : Memory w) (sep : Distinct s m) (x : ℕ)
    (outside : x∉touched s m) : prepared s m x=m x := by
  rw [prepared_eq _ _ sep]
  simp only [touched,List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
  simp_all [updates]

end Hierarchy.ProbeStage.RankUpdate

end OAI

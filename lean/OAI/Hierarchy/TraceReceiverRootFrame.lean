import OAI.Hierarchy.TraceReceiverGather

namespace OAI
/-! # Reading original S12 rows and persistent source maps at each selected root -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open BitNetwork.Ordered HistoryCompiledRows HistoryJoinScan HistoryJoinController DescriptorScan Diagonal.HistoryContraction
open HistoryReadyTape
open scoped BigOperators Fin.CommRing

variable {w : ℕ}
def Untouched (ctrl : Word w) (left : List Span) (x : ℕ) : Prop :=
  x≠ctrl.val ∧ ∀ s∈left,x< s.dest ∨ s.stop≤x

theorem cursor_after (ctrl : Word w) (left : List Span) (m : Memory w)
    (away : ∀ s∈left,ctrl.val< s.dest ∨ s.stop≤ctrl.val) :
    finish ctrl left m ctrl.val=m ctrl.val+((7*left.length:ℕ):Word w) := by
  induction left generalizing m with
  | nil => simp [finish]
  | cons s xs ih =>
    have off:=away s (List.mem_cons_self ..)
    have tail:=ih (step ctrl s m) (fun t ht=>away t (List.mem_cons_of_mem _ ht))
    rw [finish,tail]
    have keep : fillSegment s.dest (4*s.rows) (command ctrl s m).word m ctrl.val=m ctrl.val := by
      simp only [fillSegment]
      rw [ite_eq_right (by unfold Span.stop at off;omega)]
    simp only [step,bumpMemory,writeMemory,keep,List.length_cons,Nat.cast_add,Nat.cast_mul]
    push_cast
    ring

theorem fetch_after (ctrl commandPtr : Word w) (left : List Span) (m : Memory w)
    (clean : ∀ j : Fin 6,Untouched ctrl left (commandPtr+(j.val:Word w)).val) :
    fetch commandPtr (finish ctrl left m)=fetch commandPtr m := by
  have same (j : Fin 6) := preserves ctrl left m (commandPtr+(j.val:Word w)).val
    (clean j).1 (clean j).2
  unfold fetch
  congr 1
  · simpa using same (0:Fin 6)
  · simpa using same (1:Fin 6)
  · simpa using same (2:Fin 6)
  · simpa using same (3:Fin 6)
  · simpa using same (4:Fin 6)
  · simpa using same (5:Fin 6)

/-- The preceding commands may write only their own forest intervals and
increment their cursor. Source words and pin maps supplied by the actual
selected-root producer at gather entry therefore still hold at root i. -/
theorem root_at_prefix {F : Type*} {n h p : ℕ} {arity : Fin n→ℕ}
    (nets : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (tag : ((Fin 3→Bool)→F)→ℕ) (ctrl : Word w) (left : List Span) (m : Memory w)
    (head : Header ℕ) (mapPin : ℕ→ℕ) (i : Fin n) (ptr : Word w)
    (cursor0 : m ctrl.val+((7*left.length:ℕ):Word w)=ptr)
    (ctrlAway : ∀ s∈left,ctrl.val< s.dest ∨ s.stop≤ctrl.val)
    (published : fetch ptr m=head.words)
    (sizes : head.oldPins=arity i ∧ head.newPins=p ∧
      head.offset=h+∑ j : Fin i.val,(nets (Fin.castLE i.isLt.le j)).internal)
    (target : ∀ j,mapPin j.val=BitLayout.sourceAddress (resolve nets wire i (.pin j)))
    (sourceSpace : head.source+4*(nets i).cells≤2^w) (mapSpace : head.pins+head.oldPins≤2^w)
    (pinSpace : 2+head.oldPins<2^w)
    (wordSpace : ∀ row col,metadata tag (nets i) row col<2^w)
    (rows : Records tag (nets i) head.source m)
    (pins : ∀ j,j<head.oldPins→m (head.pins+j)=(mapPin j:Word w))
    (commandQuiet : ∀ j : Fin 6,Untouched ctrl left (ptr+(j.val:Word w)).val)
    (rowQuiet : ∀ (r : Fin (nets i).cells) (c : Fin 4),Untouched ctrl left (head.source+(4*r.val+c.val)))
    (pinQuiet : ∀ j,j<head.oldPins→Untouched ctrl left (head.pins+j)) :
    RootReads nets wire tag ctrl (finish ctrl left m) i head mapPin := by
  refine ⟨?_,sizes,target,sourceSpace,mapSpace,pinSpace,wordSpace,?_,?_⟩
  · rw [cursor_after ctrl left m ctrlAway,cursor0,fetch_after ctrl ptr left m commandQuiet,published]
  · intro row col
    exact (preserves ctrl left m _ (rowQuiet row col).1 (rowQuiet row col).2).trans (rows row col)
  · intro j hj
    exact (preserves ctrl left m _ (pinQuiet j hj).1 (pinQuiet j hj).2).trans (pins j hj)

/-- The numeric ranges copied to S9 follow the actual ordered list of roots. -/
def rootSpan {n : ℕ} (base : ℕ) (cells : Fin n→ℕ) (i : Fin n) : Span :=
  ⟨base+4*Tree.before cells i,cells i⟩

/-- One source observation for each elected root suffices. The second pass
uses the identical root order, and prefix sums alone separate its writes. -/
theorem canonical_locations {F : Type*} {n h p : ℕ} {arity : Fin n→ℕ}
    (nets : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (tag : ((Fin 3→Bool)→F)→ℕ) (ctrl : Word w) (base : ℕ) (m : Memory w)
    (above : ctrl.val<base ∨ base+4*(∑ i,(nets i).cells)≤ctrl.val)
    (observed : ∀ i : Fin n,∃ (head : Header ℕ) (mapPin : ℕ→ℕ),
      head.dest=(rootSpan base (fun j=>(nets j).cells) i).dest ∧
      RootReads nets wire tag ctrl
        (finish ctrl ((List.ofFn (rootSpan base fun j=>(nets j).cells)).take i.val) m) i head mapPin) :
    Locations nets wire tag ctrl m base (List.ofFn (rootSpan base fun j=>(nets j).cells)) := by
  let cells:=fun i : Fin n=>(nets i).cells
  let ss:=List.ofFn (rootSpan base cells)
  intro i
  obtain ⟨head,pin,atHead,reads⟩:=observed i
  have hi : i.val< ss.length:=by simp [ss]
  have atI : ss[i.val]=rootSpan base cells i:=by simp [ss]
  have right : ss.drop i.val = ss[i.val]::ss.drop (i.val+1):=List.drop_eq_getElem_cons hi
  have split : ss=ss.take i.val++ss[i.val]::ss.drop (i.val+1):=by
    rw [←right,List.take_append_drop]
  have atDest : head.dest=base+4*Tree.before cells i:=atHead
  refine ⟨ss.take i.val,ss.drop (i.val+1),head,pin,?_,atDest,reads,?_,?_⟩
  · rw [atI] at split
    simpa only [rootSpan,←atDest] using split
  · have endBound:=Tree.prefix_next_le cells i
    intro a lo hi
    change ctrl.val<base ∨ base+4*(∑ j,cells j)≤ctrl.val at above
    change a<head.dest+4*cells i at hi
    omega
  · intro tail inside
    obtain ⟨j,hj,eq⟩:=List.getElem_of_mem inside
    have valid : i.val+1+j<n:=by
      have hl : j<n-(i.val+1):=by simpa [ss] using hj
      omega
    let k : Fin n:=⟨i.val+1+j,valid⟩
    have atTail : tail=rootSpan base cells k:=by
      rw [←eq]
      simp [ss,List.getElem_drop,k]
    have ordered : i<k:=by change i.val < i.val+1+j;omega
    have ends:=Tree.before_end_le cells ordered
    right
    rw [atTail,atDest]
    change base+4*Tree.before cells i+4*cells i≤base+4*Tree.before cells k
    omega

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI

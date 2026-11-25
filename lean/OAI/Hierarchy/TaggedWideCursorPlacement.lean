import OAI.Hierarchy.TaggedWideCursorBoundary
import OAI.Hierarchy.TaggedWireBranchReplay

namespace OAI
/-! # Shared history pins for a chosen complete branch of the genuine prefix tree -/
noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.Prefix
open ProtocolRAM.Calendar
open scoped Classical
variable {X : Type} {slot : Event→Slot X} {es : List Event} {start : X}
local notation "P" => Prefix slot es start
local notation "C" => cursorSlot (slot:=slot) (events:=es) (x₀:=start)
local notation "root" => (Prefix.start : P es start)
local notation "V" => Cursor slot es start
local notation "Full" => Path slot es start

def boundaryIndex (j : Full) : Fin (es.length+1)↪V where
  toFun i:=boundaryState C es (atCursor root) (histories root j) i
  inj' := by
    intro i t same
    apply Fin.ext
    exact (start_boundary j i).1.symm.trans
      ((congrArg (fun x : V=>es.length-x.todo.length) same).trans (start_boundary j t).1)

private theorem append_boundary {tail x} (p:P tail x) : ∀(j:Path slot tail x)(i:Fin (tail.length+1)),
    ∃q : Fin (es.length+1),boundaryIndex (p.withSuffix j) q =
      boundaryState C tail (atCursor p) (replay p j) i := by
  induction p with
  | start=>intro j i; exact ⟨i,rfl⟩
  | @advance e tail x p c ih=>
    intro j i
    obtain ⟨q,found⟩:=ih ⟨c,j⟩ i.succ
    refine ⟨q,?_⟩
    exact found.trans (replay_boundary_succ p c j i)

theorem cursor_occurs (possible : ∀s:V,Nonempty (Path slot s.todo s.mem)) (s : V) :
    ∃j : Full,∃i,boundaryIndex j i=s := by
  obtain ⟨tail,x,p⟩:=s
  obtain ⟨j⟩:=possible ⟨tail,x,p⟩
  obtain ⟨q,found⟩:=append_boundary p j 0
  refine ⟨p.withSuffix j,q,?_⟩
  cases tail <;> exact found

private theorem replay_suffix_at : ∀{tail x}(p:P tail x)(j:Path slot tail x)(i:Fin (tail.length+1)),
    let current:=boundaryState C tail (atCursor p) (replay p j) i
    ∃back:Path slot current.todo current.mem,current.path.withSuffix back=p.withSuffix j
  | [],_,p,j,_=>⟨j,rfl⟩
  | e::tail,x,p,⟨c,j⟩,i=>by
    induction i using Fin.cases with
    | zero=>exact ⟨⟨c,j⟩,rfl⟩
    | succ i=>
      let completes (v : Cursor slot es start) : Prop :=
        ∃back : Path slot v.todo v.mem, v.path.withSuffix back = p.withSuffix ⟨c,j⟩
      change completes (boundaryState C (e::tail) (atCursor p) (replay p ⟨c,j⟩) i.succ)
      exact (congrArg completes (replay_boundary_succ p c j i)).mpr
        (replay_suffix_at (advance p c) j i)

theorem boundary_suffix (j : Full) (i : Fin (es.length+1)) :
    let current:=boundaryIndex j i
    ∃back:Path slot current.todo current.mem,current.path.withSuffix back=j :=
  replay_suffix_at root j i

variable {D : Cursor slot es start → Type} {Q : Type}
private theorem chooseAt (selected : Full)
    (possible : ∀s:V,Nonempty (Path slot s.todo s.mem))
    (rows : ∀(j:Full)(i:Fin (es.length+1)), D (boundaryIndex j i)↪Q)
    (s : V) : ∃g:D s↪Q,∀i,(h : boundaryIndex selected i=s)→
      cast (congrArg (fun v => D v ↪ Q) h) (rows selected i) = g := by
  classical
  by_cases here : s∈Set.range (boundaryIndex selected)
  · obtain ⟨i,rfl⟩:=here
    refine ⟨rows selected i,?_⟩
    intro k hit
    obtain rfl:=(boundaryIndex selected).injective hit
    rfl
  · obtain ⟨j,i,rfl⟩:=cursor_occurs possible s
    exact ⟨rows j i,fun t h=>(here ⟨t,h⟩).elim⟩

/-- All off-branch cursors have an actual continuation. This supplies a total
function of the cursor without imposing any agreement on future purchases. -/
def rowPlacement (selected : Full) (possible : ∀s:V,Nonempty (Path slot s.todo s.mem))
    (rows : ∀(j:Full)(i:Fin (es.length+1)), D (boundaryIndex j i)↪Q)
    (s : V) : D s↪Q := Classical.choose (chooseAt selected possible rows s)

theorem rowPlacement_boundary (selected : Full) (possible : ∀s:V,Nonempty (Path slot s.todo s.mem))
    (rows : ∀(j:Full)(i:Fin (es.length+1)), D (boundaryIndex j i)↪Q) (i : Fin (es.length+1)) :
    rowPlacement selected possible rows (boundaryIndex selected i)=rows selected i :=
  ((Classical.choose_spec (chooseAt selected possible rows (boundaryIndex selected i))) i rfl).symm

end Hierarchy.WireTelescope.CalendarTape.Prefix

end
end OAI

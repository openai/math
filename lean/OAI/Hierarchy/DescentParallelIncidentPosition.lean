import OAI.Hierarchy.DescentParallelBase
import OAI.Hierarchy.DescentSharedCableSiblings

namespace OAI
/-! # Absolute local incidence slots of all children, including previous tethers -/
namespace Hierarchy.DescentParallelBase.Incidence
open DescentSharedCableNames
open scoped Classical BigOperators
noncomputable section
variable {U E : Type} [DecidableEq U] [Fintype E] {n cap : ℕ}
variable (B : Ends U n) (h : U)

def hit (src dst : U) :=decide (src=h ∨ dst=h)
def marks : Ends Bool n :=⟨fun i=>hit h (B.src i) (B.dst i),fun i=>hit h (B.src i) (B.dst i)⟩

/-- Absolute signed-slot index is a shared serial in the physical tape
with all incident neighbors identified at this one receiver. -/
theorem position (fit : ∀u,(B.incident u).card≤cap) (e : ↥(B.incident h)) :
    (B.position fit h e).val=(marks B h).serial true true e.val:=by
  let o:=B.ordinal h
  let xs:=(Finset.univ.filter (fun u:↥(B.incident h)=>u.val<e.val))
  have numbered:xs.map o.toEquiv.toEmbedding=Finset.Iio (o e):=by
    ext j;obtain ⟨u,rfl⟩:=o.surjective j;simp [xs,o.lt_iff_lt]
  have original:xs.map (Function.Embedding.subtype (·∈B.incident h))=(marks B h).earlier true true e.val:=by
    ext q
    rw [Finset.mem_map]
    change (∃u∈xs,(u:Fin n)=q) ↔ _
    simp only [xs,Finset.mem_filter,Finset.mem_univ,true_and,Ends.earlier,Ends.parallel,marks,hit,decide_eq_true_eq,and_self,or_self]
    constructor
    · rintro ⟨u,before,rfl⟩;exact ⟨(Finset.mem_filter.mp u.property).2,before⟩
    · rintro ⟨at_,before⟩;exact ⟨⟨q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,at_⟩⟩,before,rfl⟩
  change (o e).val=((marks B h).earlier true true e.val).card
  rw [←original,Finset.card_map];simpa only [Finset.card_map,Fin.card_Iio] using (congrArg Finset.card numbered).symm

variable {B} (C : Blocks B E)

def collapse (h : U) : Blocks (marks B h) E where
  count:=C.count
  first:=C.first
  src f:=hit h (C.src f) (C.dst f)
  dst f:=hit h (C.src f) (C.dst f)
  order:=C.order
  consecutive:=C.consecutive
  atSource f j:=by simp [marks,C.atSource,C.atTarget]
  atTarget f j:=by simp [marks,C.atSource,C.atTarget]

def candidate (h : U) (e : Local C h) (j : Fin (C.count e.val)) : ↥(B.incident h):=
  ⟨C.order ⟨e.val,j⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [C.atSource,C.atTarget] using e.property.2⟩⟩

theorem initial (h : U) (fit : ∀u,(B.incident u).card≤cap) (e : Local C h) :
    (B.position fit h (candidate C h e ⟨0,e.property.1⟩)).val=
     ∑f:E,if (C.src f=h ∨ C.dst f=h) ∧ C.first f<C.first e.val then C.count f else 0 :=by
  have live : decide (C.src e.val=h ∨ C.dst e.val=h)=true := decide_eq_true e.property.2
  rw [position B h]
  change (marks B h).serial true true (C.order ⟨e.val,⟨0,e.property.1⟩⟩) = _
  have sum := (collapse C h).first_serial e.val e.property.1
  simp only [collapse,Blocks.parallel,hit,live,decide_eq_true_eq,and_self,or_self] at sum
  refine sum.trans (Finset.sum_congr rfl ?_)
  intro f _
  by_cases earlier : (C.src f=h ∨ C.dst f=h) ∧ C.first f<C.first e.val
  · simp only [ite_eq_left earlier]
  · simp only [ite_eq_right earlier]

omit [Fintype E] in
theorem child (h : U) (fit : ∀u,(B.incident u).card≤cap) (e : Local C h) (j : Fin (C.count e.val)) :
    (B.position fit h (candidate C h e j)).val=(B.position fit h (candidate C h e ⟨0,e.property.1⟩)).val+j.val :=by
  rw [position B h,position B h]
  have marked (t : Fin (C.count e.val)) : C.order ⟨e.val,t⟩∈(marks B h).parallel true true:=by simp [marks,Ends.parallel,hit,C.atSource,C.atTarget,e.property.2]
  change (marks B h).serial true true (C.order ⟨e.val,j⟩)=(marks B h).serial true true (C.order ⟨e.val,⟨0,e.property.1⟩⟩)+j.val
  obtain ⟨i,lim⟩:=j;induction i with
  | zero=>simp
  | succ i ih=>
    let a:Fin (C.count e.val):=⟨i,by omega⟩;let b:Fin (C.count e.val):=⟨i+1,lim⟩
    have step:(C.order ⟨e.val,b⟩).val=(C.order ⟨e.val,a⟩).val+1:=by rw [C.consecutive,C.consecutive];change C.first e.val+(i+1)=C.first e.val+i+1;omega
    exact (Siblings.serial_next (marks B h) true true _ _ (marked a) step).trans
      ((congrArg (fun k : ℕ=>k+1) (ih a.isLt)).trans (Nat.add_assoc _ i 1))

omit [Fintype E] in
/-- The shared parallel-wire serial also advances by one per paid finer
grain; unlike `position` its earlier rows have exactly the same peer. -/
theorem parallel_child (e : E) (j : Fin (C.count e)) :
    B.serial (C.src e) (C.dst e) (C.order ⟨e,j⟩)=B.serial (C.src e) (C.dst e) (C.order ⟨e,⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩)+j.val :=by
  have marked (u : Fin (C.count e)) : C.order ⟨e,u⟩∈B.parallel (C.src e) (C.dst e):=by simp [Ends.parallel,C.atSource,C.atTarget]
  obtain ⟨i,lim⟩:=j;induction i with
  | zero=>simp
  | succ i ih=>
    let a:Fin (C.count e):=⟨i,by omega⟩;let b:Fin (C.count e):=⟨i+1,lim⟩
    have step:(C.order ⟨e,b⟩).val=(C.order ⟨e,a⟩).val+1:=by rw [C.consecutive,C.consecutive];change C.first e+(i+1)=C.first e+i+1;omega
    exact (Siblings.serial_next B (C.src e) (C.dst e) _ _ (marked a) step).trans
      ((congrArg (fun k : ℕ=>k+1) (ih a.isLt)).trans (Nat.add_assoc _ i 1))

end
end Hierarchy.DescentParallelBase.Incidence

end OAI

import OAI.Hierarchy.DescentBundleTagKeys

namespace OAI
/-! # Constructing the scalar name from the primitive role and its active rectangular slice fields -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentBundleHistory DescentEpochTagKeys
noncomputable section
variable {U : Type} {n A G p R : ℕ}

/-- Every address here is local to one bounded node. Unused entries can contain arbitrary data. -/
structure Fields (A G : ℕ) where
  primitive : ℕ
  arity : ℕ
  groups : Fin A→ℕ
  triple : Fin G→SliceCode

def counts (x : Fields A G) := List.ofFn fun j : Fin (min A x.arity)=>x.groups (j.castLE (min_le_left ..))
def triples (x : Fields A G) := List.ofFn fun j : Fin (min G (counts x).sum)=>x.triple (j.castLE (min_le_left ..))
def metadata (x : Fields A G) := (counts x).splitLengths (triples x)

structure Printed (old : Codec U n) (x : Fields A G) (role : U) (slices : List (List SliceCode)) : Prop where
  primitive : x.primitive=(old.store role).val+1
  arity : x.arity=slices.length
  operands : slices.length≤A
  slicesFit : slices.flatten.length≤G
  groups : ∀j:Fin slices.length,x.groups (j.castLE operands)=slices[j].length
  triples : ∀j:Fin slices.flatten.length,x.triple (j.castLE slicesFit)=slices.flatten[j]

private theorem length_sum (xs : List (List SliceCode)) : (xs.map List.length).sum=xs.flatten.length := by
  exact List.length_flatten.symm

theorem metadata_read (old : Codec U n) (x : Fields A G) (role : U) (xs : List (List SliceCode))
    (physical : Printed old x role xs) : metadata x=xs := by
  have headers : counts x=xs.map List.length := by
    apply List.ext_getElem
    · simp [counts,physical.arity,min_eq_right physical.operands]
    · intro j l r
      have hj : j<xs.length:=by simpa using r
      simp only [counts,List.getElem_ofFn,List.getElem_map]
      exact physical.groups ⟨j,hj⟩
  have total : (counts x).sum=xs.flatten.length := by
    rw [headers,length_sum]
  have serialized : triples x=xs.flatten := by
    apply List.ext_getElem
    · simp only [triples,List.length_ofFn,total,min_eq_right physical.slicesFit]
    · intro j l r
      simp only [triples,List.getElem_ofFn]
      exact physical.triples ⟨j,r⟩
  rw [metadata,headers,serialized,regroup]

def written (old : Codec U n) (p R : ℕ) (x : Fields A G) : ℕ :=
  if h : 0<x.primitive ∧ x.primitive≤n then
    ((DescentBundleTagKeys.codec old A G p R).store (old.read ⟨x.primitive-1,by omega⟩,metadata x)).val+1
  else 0

theorem written_read (old : Codec U n) (x : Fields A G) (t : U) (xs : List (List SliceCode))
    (roleFit : old.fits t) (issued : Printed old x t xs) :
    written old p R x=((DescentBundleTagKeys.codec old A G p R).store (t,xs)).val+1 := by
  have small:=(old.store t).isLt
  rw [written,dite_eq_left (by have:=issued.primitive;omega),metadata_read old x t xs issued]
  have index : (⟨x.primitive-1,by have:=issued.primitive;omega⟩:Fin n)=old.store t := by
    apply Fin.ext
    change x.primitive-1=(old.store t).val
    rw [issued.primitive,Nat.add_sub_cancel]
  rw [index,old.read_store _ roleFit]

theorem written_bound (old : Codec U n) (x : Fields A G) :
    written old p R x≤DescentBundleTagKeys.capacity n A G p R := by
  unfold written
  split
  · exact Nat.succ_le_of_lt (Fin.isLt _)
  · exact Nat.zero_le _

theorem empty (old : Codec U n) (x : Fields A G) (blank : x.primitive=0) : written old p R x=0 := by simp [written,blank]


end
end Hierarchy.DescentTerminalCombinedRole

end OAI

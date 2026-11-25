import OAI.Hierarchy.DescentColonyLayout
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # A binary row operation pulls each packed output from at most two packed inputs -/
namespace Hierarchy.DescentGLPacked
open DescentGL DescentColonies DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {h l b : ℕ}

structure Route (A I : Type) where
  left : A→A
  right : A→A
  family : A→Bool
  select : Bool→I→Bool
  localAt : Bool→I→I

def Route.pull {A I : Type} (R : Route A I) (x : A×I) : A×I :=
  let f:=R.family x.1
  (if R.select f x.2 then R.right x.1 else R.left x.1,R.localAt f x.2)

theorem zeroOne (z : ZMod 2) : z=0 ∨ z=1 := by
  fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl

def bit (z : ZMod 2) := decide (z≠0)

@[simp] theorem add_bit (v z : ZMod 2) : (if bit z then v+1 else v)=v+z := by
  rcases zeroOne z with rfl|rfl <;> simp [bit]

def bump {k : ℕ} (x : Bits k) (i : Fin k) (z : ZMod 2) : Bits k :=
  Function.update x i (x i+z)

@[simp] theorem bump_zero {k : ℕ} (x : Bits k) (i : Fin k) : bump x i 0=x := by simp [bump]

theorem bump_bit {k : ℕ} (x : Bits k) (i : Fin k) (z : ZMod 2) :
    (if bit z then bump x i 1 else x)=bump x i z := by
  rcases zeroOne z with rfl|rfl <;> simp [bit]

abbrev Place (h l : ℕ) := Fin h⊕Fin l

def coordinate (x : Bits h×Bits l) : Place h l→ZMod 2 := Sum.elim x.1 x.2

def addAt (t : Place h l) (x : Bits h×Bits l) (z : ZMod 2) : Bits h×Bits l :=
  match t with
  | .inl i=>(bump x.1 i z,x.2)
  | .inr i=>(x.1,bump x.2 i z)

def xorRoute (t s : Place h l) : Route (Bits h) (Bits l) :=
  match t,s with
  | .inl i,.inl j=>⟨fun a=>bump a i (a j),id,fun _=>false,fun _ _=>false,fun _=>id⟩
  | .inl i,.inr j=>⟨id,fun a=>bump a i 1,fun _=>false,fun _ y=>bit (y j),fun _=>id⟩
  | .inr i,.inl j=>⟨id,id,fun a=>bit (a j),fun _ _=>false,fun f y=>if f then bump y i 1 else y⟩
  | .inr i,.inr j=>⟨id,id,fun _=>false,fun _ _=>false,fun _ y=>bump y i (y j)⟩

theorem xor_pull (t s : Place h l) (x : Bits h×Bits l) :
    (xorRoute t s).pull x=addAt t x (coordinate x s) := by
  obtain ⟨u,v⟩:=x
  cases t <;> cases s <;> simp [xorRoute,Route.pull,addAt,coordinate,bump_bit]
  exact bump_bit ..

/-- The linear map acts with the first h coordinates named by the word address. -/
theorem append_addAt (t : Place h l) (x : Bits h×Bits l) (z : ZMod 2) :
    Fin.append (addAt t x z).1 (addAt t x z).2=
      bump (Fin.append x.1 x.2) (finSumFinEquiv t) z := by
  obtain ⟨u,v⟩:=x
  funext i
  cases t with
  | inl j=>
    refine Fin.addCases (fun a=>?_) (fun a=>?_) i
    · by_cases hit:a=j
      · subst a;simp [addAt,bump]
      · simp [addAt,bump,Function.update,hit]
    · have ne : Fin.natAdd h a≠Fin.castAdd l j := by
        intro eq;have v:=congrArg Fin.val eq;change h+a.val=j.val at v;omega
      simp [addAt,bump,Function.update,ne]
  | inr j=>
    refine Fin.addCases (fun a=>?_) (fun a=>?_) i
    · have ne : Fin.castAdd l a≠Fin.natAdd h j := by
        intro eq;have v:=congrArg Fin.val eq;change a.val=h+j.val at v;omega
      simp [addAt,bump,Function.update,ne]
    · by_cases hit:a=j
      · subst a;simp [addAt,bump]
      · simp [addAt,bump,Function.update,hit]

theorem append_xor (t s : Place h l) (x : Bits h×Bits l) :
    let out:=(xorRoute t s).pull x
    Fin.append out.1 out.2=bump (Fin.append x.1 x.2) (finSumFinEquiv t) ((Fin.append x.1 x.2) (finSumFinEquiv s)) := by
  dsimp only
  rw [xor_pull,append_addAt]
  cases s <;> simp [coordinate]

/-- Concatenating high and low coordinates is precisely the physical contiguous order. -/
theorem value_append (x : Bits h) (y : Bits l) :
    value (h+l) (Fin.append x y)=value h x*2^l+value l y := by
  induction l with
  | zero=>
    have same : Fin.append x y=x := by funext i;exact Fin.append_left x y i
    simp [same,value]
  | succ l ih=>
    let tail:=DescentGL.headRows (Nat.le_succ l) y
    have head : DescentGL.headRows (Nat.le_succ (h+l)) (Fin.append x y)=Fin.append x tail := by
      funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      · exact (Fin.append_left x y j).trans (Fin.append_left x tail j).symm
      · exact (Fin.append_right x y (j.castSucc)).trans (Fin.append_right x tail j).symm
    have last : Fin.append x y (Fin.last (h+l))=y (Fin.last l) := Fin.append_right x y (Fin.last l)
    change 2*value (h+l) _+_=value h x*2^(l+1)+(2*value l tail+_)
    rw [head,ih,pow_succ]
    have finalBit:=congrArg ZMod.val last
    change (Fin.append x y (Fin.last (h.add l))).val=(y (Fin.last l)).val at finalBit
    nlinarith only [finalBit]

theorem address_append (x : Bits h) (y : Bits l) :
    ((address (h+l)) (Fin.append x y)).val=((address h) x).val*2^l+((address l) y).val :=
  value_append x y

end
end Hierarchy.DescentGLPacked

end OAI

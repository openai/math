import OAI.Hierarchy.DescentKernelHistory
import OAI.Hierarchy.DescentCableUnbundling
import OAI.Hierarchy.DescentQuotientHistory
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Readdressing retained local tensors under the physical split into equal-width cables -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section

def cutWords : List ℕ → List (List Bool) → List (List Bool)
  | [],_=>[]
  | n::ns,words=>(words.take n).flatten :: cutWords ns (words.drop n)

theorem cut_exact {α : Type} (x : α→List Bool) (groups : List (List α)) :
    cutWords (groups.map List.length) (groups.flatten.map x)=groups.map (fun ms=>ms.flatMap x) := by
  induction groups with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,List.flatten_cons,List.map_append,cutWords]
    have a : g.length=(g.map x).length := (List.length_map ..).symm
    rw [a,List.take_left,List.drop_left,ih]
    rfl

variable {A B C : Type} (r : Recipe A B) (parts : B→List C)
def physicalArgs (v : r.Node) := List.ofFn fun j=>match r.operand v j with
  | .inr hidden=>[Sum.inr hidden]
  | .inl b=>(parts b).map (Sum.inl : C→C⊕r.Hidden)

def splitLanes : Recipe (A×List ℕ) C where
  Hidden := r.Hidden
  width := r.width
  Node := r.Node
  tag v := (r.tag v,(physicalArgs r parts v).map List.length)
  arity v := (physicalArgs r parts v).flatten.length
  operand v j := (physicalArgs r parts v).flatten[j.val]

variable {F : Type*} [CommSemiring F] (scalar : A→List (List Bool)→F)

def laneScalar (q : A×List ℕ) (words : List (List Bool)) := scalar q.1 (cutWords q.2 words)

theorem splitLanes_value (read : C→List Bool) :
    (splitLanes r parts).value (laneScalar scalar) read=r.value scalar (fun b=>(parts b).flatMap read) := by
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro v _
  let x : C⊕r.Hidden→List Bool := Sum.elim read (fun h=>wordList (y h))
  let groups := physicalArgs r parts v
  change scalar (r.tag v) (cutWords (groups.map List.length)
    (List.ofFn (fun j : Fin groups.flatten.length=>x groups.flatten[j.val])))=_
  rw [List.ofFn_getElem_eq_map,cut_exact]
  congr 1
  unfold groups physicalArgs
  rw [←List.ofFn_comp']
  congr 1
  funext j
  cases h : r.operand v j <;> simp [x,List.flatMap_map]; rfl

/-- The scalar matures into a larger address descriptor, but no new
occurrence tensor is created by cutting one cable into several lanes. -/
theorem splitLanes_atoms : Fintype.card (splitLanes r parts).Node=Fintype.card r.Node := rfl

variable {D : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits) (core : Finset N.Edge)
variable (m : N.Edge→ℕ) (q : ℕ) (fit : ∀e∈core,N.width e=m e*q)
local notation "Fine" => network N core m q

def laneNames (v : N.Site) : Boundary N v→List (Boundary (Fine) v)
  | .inr p=>[.inr p]
  | .inl e=> if h : e.1∈core then List.ofFn (fun i : Fin (m e.1)=>
      Sum.inl ⟨.inr ⟨⟨e.1,h⟩,i⟩,e.2⟩) else [.inl ⟨.inl ⟨e.1,h⟩,e.2⟩]

theorem joined {a b w : ℕ} (h : w=a*b) (rows : Fin a→Word b) :
    wordList ((splitWord h).symm rows)=(List.ofFn (fun j=>wordList (rows j))).flatten := by
  subst w
  rw [wordList,List.ofFn_mul]
  congr 1
  congr 1
  funext j
  congr 1
  funext k
  change rows (finProdFinEquiv.symm _).1 (finProdFinEquiv.symm _).2=rows j k
  have bound : j.val*b+k.val<a*b :=
    (Nat.add_lt_add_left k.isLt _).trans_le (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right b j.isLt)
  have coordinate : (⟨j.val*b+k.val,bound⟩ : Fin (a*b))=finProdFinEquiv (j,k) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [coordinate,Equiv.symm_apply_apply]

theorem split_represents (T : N.Tables F) (old : ∀v,Recipe A (Boundary N v))
    (rep : Represents N scalar T old) :
    Represents (Fine) (laneScalar scalar) (DescentCableUnbundling.tables N core m q fit T)
      (fun v=>splitLanes (old v) (laneNames N core m q v)) := by
  intro v read pins
  rw [splitLanes_value]
  unfold DescentCableUnbundling.tables
  rw [←rep]
  congr 1
  funext t
  cases t with
  | inr p=>simp [input,laneNames]
  | inl e=>
    by_cases h : e.1∈core
    · simp only [laneNames,h,dite_eq_left,input,Sum.elim_inl]
      simp [List.flatMap,Function.comp_def,h]
      exact (joined (fit e.val h) (fun i=>read ⟨.inr ⟨⟨e.val,h⟩,i⟩,e.property⟩)).symm
    · simp [laneNames,input,h]

end
end Hierarchy.DescentKernelHistory

end OAI

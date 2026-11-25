import Mathlib.Data.List.GetD
import OAI.Hierarchy.DescentHistoryLanes

namespace OAI
/-! # Bit-addressed local histories for bundles with changing word boundaries -/

namespace Hierarchy.DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {A B C Tag F : Type} [CommSemiring F]

/-- A localized bit selector is a scalar-address datum. `none` leaves a
private word available to the local tensor without reindexing it. -/
def selectWord : Option ℕ→List Bool→List Bool
  | none,w=>w
  | some i,w=>[w.getD i false]

def sliceRecipe (r : Recipe Tag (B×ℕ)) : Recipe (Tag×List (Option ℕ)) B :=
  {r with
    tag := fun v=>(r.tag v,List.ofFn fun j=>(r.operand v j).elim (some ∘ Prod.snd) (fun _=>none))
    operand := fun v j=>(r.operand v j).map Prod.fst id}

def sliceScalar (scalar : Tag→List (List Bool)→F) (x : Tag×List (Option ℕ)) (ws : List (List Bool)) :=
  scalar x.1 (x.2.zipWith selectWord ws)

theorem slice_value (r : Recipe Tag (B×ℕ)) (scalar : Tag→List (List Bool)→F) (x : B→List Bool) :
    (sliceRecipe r).value (sliceScalar scalar) x=
      r.value scalar (fun p=>[(x p.1).getD p.2 false]) := by
  unfold Recipe.value
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro v _
  unfold sliceScalar
  apply congrArg (scalar (r.tag v))
  change (List.ofFn fun j=>(r.operand v j).elim (some ∘ Prod.snd) (fun _=>none)).zipWith selectWord
      (List.ofFn fun j=>((r.operand v j).map Prod.fst id).elim x (fun i=>wordList (h i)))=_
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipWith,List.getElem_ofFn]
    cases ht : r.operand v ⟨i,by simpa using hj⟩ <;> rfl

/-- Each original argument is fetched from a list of actual local wire
coordinates. These lists permit arbitrary ordering and repeated reads. -/
def bitWiring (r : Recipe Tag A) (portRefs : A→List (B×ℕ)) :=
  sliceRecipe (splitLanes r portRefs)

def wiredScalar (scalar : Tag→List (List Bool)→F) :=
  sliceScalar (laneScalar scalar)

theorem wiring_value (r : Recipe Tag A) (portRefs : A→List (B×ℕ))
    (scalar : Tag→List (List Bool)→F) (x : B→List Bool) :
    (bitWiring r portRefs).value (wiredScalar scalar) x=
    r.value scalar (fun a=>(portRefs a).map (fun p=>(x p.1).getD p.2 false)) := by
  rw [bitWiring,wiredScalar,slice_value,splitLanes_value]
  congr 1
  funext a
  generalize portRefs a=l
  induction l with
  | nil=>rfl
  | cons p xs ih=>exact congrArg (List.cons ((x p.1).getD p.2 false)) ih

/-- The typed form uses an actual physical bit on both sides. Because
the output program references finite positions, no out-of-range pad enters a scalar. -/
abbrev BitRef (w : A→ℕ) := Σa,Fin (w a)

def bitPorts (old : A→ℕ) (new : B→ℕ) (which : BitRef old→BitRef new)
    (a : A) : List (B×ℕ) := List.ofFn fun j=>
  let s:=which ⟨a,j⟩
  (s.1,s.2.val)

theorem typed_wiring (r : Recipe Tag A) (old : A→ℕ) (new : B→ℕ) (which : BitRef old→BitRef new)
    (scalar : Tag→List (List Bool)→F) (x : ∀b,Word (new b)) :
    (bitWiring r (bitPorts old new which)).value (wiredScalar scalar) (fun b=>wordList (x b))=
      r.value scalar (fun a=>wordList fun j=>x (which ⟨a,j⟩).1 (which ⟨a,j⟩).2) := by
  rw [wiring_value]
  congr 1
  funext a
  unfold bitPorts wordList
  rw [←List.ofFn_comp']
  apply congrArg List.ofFn
  funext j
  simp []

end
end Hierarchy.DescentKernelHistory

end OAI

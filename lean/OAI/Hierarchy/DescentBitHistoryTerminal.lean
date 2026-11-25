import OAI.Hierarchy.DescentFiniteWordRead
import OAI.Hierarchy.DescentBoundedBitHistory

namespace OAI
/-! # Final word-port representation of an exactly bit-addressed atom history -/

namespace Hierarchy.DescentKernelHistory.BitRecipe
open scoped Classical BigOperators
noncomputable section
variable {Tag A F : Type} [CommSemiring F] {w : A→ℕ} (r : BitRecipe Tag A w)
variable (scalar : Tag→List (List Bool)→F)

private def forgetBit : BitRef w ⊕ BitRef r.hiddenWidth→(A⊕r.Hidden)×ℕ
  | .inl a=>(.inl a.1,a.2.val)
  | .inr h=>(.inr h.1,h.2.val)

def operands (u : r.Node) := List.ofFn fun j=>List.ofFn fun t=>forgetBit r (r.arg u j t)

def asRecipe : Recipe ((Tag×List ℕ)×List ℕ) A where
  Hidden := r.Hidden
  width := r.hiddenWidth
  Node := r.Node
  arity u := (operands r u).flatten.length
  tag u := ((r.tag u,(operands r u).map List.length),(operands r u).flatten.map Prod.snd)
  operand u j := (operands r u).flatten[j.val].1

def gatheredScalar (t : (Tag×List ℕ)×List ℕ) (ws : List (List Bool)) : F :=
  scalar t.1.1 (cutWords t.1.2 (t.2.zipWith (fun j x=>[x.getD j false]) ws))

theorem asRecipe_value (x : ∀a,Word (w a)) :
    (asRecipe r).value (gatheredScalar scalar) (fun a=>wordList (x a))=
      r.value scalar (fun i=>x i.1 i.2) := by
  unfold Recipe.value value
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro u _
  let get : (A⊕r.Hidden)×ℕ→Bool := fun t=>(t.1.elim (fun a=>wordList (x a)) (fun e=>wordList (h e))).getD t.2 false
  let t := (operands r u).flatten
  let read : A⊕r.Hidden→List Bool := Sum.elim (fun a=>wordList (x a)) (fun e=>wordList (h e))
  have fetch : List.ofFn (fun j : Fin t.length=>read t[j.val].1)=t.map (read ∘ Prod.fst) := by
    apply List.ext_getElem <;> simp [Function.comp_def]
  have zipped : (t.map Prod.snd).zipWith (fun j bits=>[bits.getD j false]) (t.map (read ∘ Prod.fst))=
      t.map (fun p=>[get p]) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [get,read,Function.comp_def]; rfl
  unfold gatheredScalar
  apply congrArg (scalar (r.tag u))
  change cutWords ((operands r u).map List.length)
    ((t.map Prod.snd).zipWith (fun j bits=>[bits.getD j false]) (List.ofFn (fun j : Fin t.length=>read t[j.val].1)))=_
  rw [fetch,zipped,cut_exact]
  simp only [operands,←List.ofFn_comp']
  apply congrArg List.ofFn
  funext j
  unfold wordList
  rw [←List.map_eq_flatMap,←List.ofFn_comp']
  apply congrArg List.ofFn
  funext k
  cases entry : r.arg u j k with
  | inl a =>
    simp only [get,forgetBit,Sum.elim_inl,wordList]
    change (List.ofFn (x a.1)).getD a.2.val false=x a.1 a.2
    exact finiteWord_read (x a.1) a.2 false
  | inr e =>
    simp only [get,forgetBit,Sum.elim_inr,wordList]
    change (List.ofFn (h e.1)).getD e.2.val false=h e.1 e.2
    exact finiteWord_read (h e.1) e.2 false

theorem asRecipe_arity (u : r.Node) : (asRecipe r).arity u=r.nodeBits u := by
  simp [asRecipe,operands,nodeBits,List.length_flatten,List.sum_ofFn]

end
end Hierarchy.DescentKernelHistory.BitRecipe

end OAI

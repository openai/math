import OAI.Hierarchy.DescentBitHistory

namespace OAI
/-! # Bit-addressed atom histories whose operand counts are stable under rerouting -/

namespace Hierarchy.DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {A B Tag F : Type} [CommSemiring F]

/-- A node retains its original operand lengths. Each bit has either a
physical boundary coordinate or a local summation coordinate. Readdressing
a word never copies the surrounding word into the node's description. -/
structure BitRecipe (Tag A : Type) (width : A→ℕ) where
  Hidden : Type
  [hiddenFinite : Fintype Hidden]
  hiddenWidth : Hidden→ℕ
  Node : Type
  [nodeFinite : Fintype Node]
  tag : Node→Tag
  arity : Node→ℕ
  size : (u : Node)→Fin (arity u)→ℕ
  arg : (u : Node)→(j : Fin (arity u))→Fin (size u j)→BitRef width⊕BitRef hiddenWidth

attribute [instance] BitRecipe.hiddenFinite BitRecipe.nodeFinite

namespace BitRecipe
variable {width : A→ℕ} {nextWidth : B→ℕ} {S : Type}
variable (r : BitRecipe Tag A width) (scalar : Tag→List (List Bool)→F)
def value (read : BitRef width→Bool) : F :=
  ∑h : (i : r.Hidden)→Word (r.hiddenWidth i),∏u : r.Node,scalar (r.tag u)
    (List.ofFn fun j=>wordList fun t=>(r.arg u j t).elim read (fun z=>h z.1 z.2))

def reroute (route : BitRef width→BitRef nextWidth) : BitRecipe Tag B nextWidth :=
  {r with arg := fun u j t=>(r.arg u j t).map route id}

theorem reroute_eval (route : BitRef width→BitRef nextWidth) (read : BitRef nextWidth→Bool) :
    (r.reroute route).value scalar read=r.value scalar (read ∘ route) := by
  unfold value
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro u _
  apply congrArg (scalar (r.tag u))
  apply congrArg List.ofFn
  funext j
  apply congrArg wordList
  funext t
  change ((r.arg u j t).map route id).elim read _=(r.arg u j t).elim (read ∘ route) _
  cases r.arg u j t <;> rfl

def retag (f : Tag→S) : BitRecipe S A width := {r with tag := f ∘ r.tag}

theorem retag_eval (f : Tag→S) (s : S→List (List Bool)→F) (read : BitRef width→Bool) :
    (r.retag f).value s read=r.value (s ∘ f) read := rfl

def referenceWidth (r : Recipe Tag A) (w : A→ℕ) : A⊕r.Hidden→ℕ := Sum.elim w r.width

def exposeRef (r : Recipe Tag A) (w : A→ℕ) : (p : A⊕r.Hidden)→
    Fin (referenceWidth r w p)→BitRef w⊕BitRef r.width
  | .inl x,j=>.inl ⟨x,j⟩
  | .inr x,j=>.inr ⟨x,j⟩

def expose (r : Recipe Tag A) (w : A→ℕ) : BitRecipe Tag A w where
  Hidden := r.Hidden
  hiddenWidth := r.width
  Node := r.Node
  tag := r.tag
  arity := r.arity
  size u j := referenceWidth r w (r.operand u j)
  arg u j := exposeRef r w (r.operand u j)

theorem expose_eval (r : Recipe Tag A) (w : A→ℕ) (read : ∀a,Word (w a)) :
    (expose r w).value scalar (fun i=>read i.1 i.2)=r.value scalar (fun a=>wordList (read a)) := by
  unfold value Recipe.value
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro u _
  apply congrArg (scalar (r.tag u))
  apply congrArg List.ofFn
  funext j
  change wordList (fun t=>(exposeRef r w (r.operand u j) t).elim _ _)=_
  cases r.operand u j <;> rfl

/-- The number of bit references is determined exactly at birth. -/
def nodeBits (u : r.Node) := ∑j,r.size u j

@[simp] theorem reroute_bits (route : BitRef width→BitRef nextWidth) (u : r.Node) :
    (r.reroute route).nodeBits u=r.nodeBits u := rfl

end BitRecipe
end
end Hierarchy.DescentKernelHistory

end OAI

import OAI.Computability.VPVNP.Classes
import OAI.Computability.VPVNP.ParseEvents
import OAI.Computability.VPVNP.ParseGrammar

/-! # Weights of the interval events in an ordered parse

Each production occurrence contributes its grammar scalar. Each leaf also contributes
its input value. The interval coordinate distinguishes repeated occurrences of the same
production. Consequently a product over the finite event table counts these repetitions
with the same multiplicity as the recursive parse weight.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open MvPolynomial OrderedParse

variable {R S V H : Type*} {n : ℕ} [CommSemiring R]

/-- Scalar of a terminal or binary production. A binary coordinate outside the
layer or split bounds of the grammar receives zero. -/
def eventScalar (G : ParseGrammar R V H n) (e : ParseEvent V H) : R :=
  match e.production with
  | .inl v => G.terminal e.state v
  | .inr (b, i, j) =>
    if hd : e.layer < n then
      if hb : b < e.layer then G.binary ⟨e.layer, hd⟩ e.state ⟨b, hb⟩ i j else 0
    else 0

/-- Optional variable supplied by a leaf production. -/
def ParseEvent.leafVariable? (e : ParseEvent V H) : Option V :=
  e.production.elim some (fun _ => none)

/-- A terminal contributes its input value, and a binary production contributes one. -/
def ParseEvent.leafValue [One S] (e : ParseEvent V H) (input : V → S) : S :=
  e.leafVariable?.elim 1 input

/-- Multiplying the selected production scalars recovers the recursively defined
parse weight, independently of the left endpoint of the root interval. -/
theorem prod_eventScalar (G : ParseGrammar R V H n) {d : ℕ} (t : OrderedParse V H d)
    (hd : d < n) (l : ℕ) (h : H) :
    ∏ e ∈ t.events l h, G.eventScalar e = G.weight ⟨d, hd⟩ h t := by
  classical
  induction t generalizing l h with
  | leaf v => simp [events, rootEvent, eventScalar]
  | @node k b i j left right ih₁ ih₂ =>
    rw [events, Finset.prod_insert (rootEvent_notMem_children b i j left right l h),
      Finset.prod_union (disjoint_childEvents b i j left right l), weight_node]
    have hleft := (leftDegree ⟨k + 1, hd⟩ b).isLt
    have hright := (rightDegree ⟨k + 1, hd⟩ b).isLt
    rw [ih₁ hleft, ih₂ hright]
    simp [eventScalar, rootEvent, hd, b.isLt, mul_assoc, leftDegree, rightDegree]

/-- The product of the leaf inputs over the event table is the product of the
parse's left-to-right list of leaves. -/
theorem prod_leafValue [CommMonoid S] (input : V → S) {d : ℕ} (t : OrderedParse V H d)
    (l : ℕ) (h : H) :
    ∏ e ∈ t.events l h, e.leafValue input = (t.leaves.map input).prod := by
  classical
  induction t generalizing l h with
  | leaf v => simp [events, rootEvent, ParseEvent.leafValue, ParseEvent.leafVariable?, leaves]
  | node b i j left right ih₁ ih₂ =>
    rw [events, Finset.prod_insert (rootEvent_notMem_children b i j left right l h),
      Finset.prod_union (disjoint_childEvents b i j left right l), ih₁, ih₂]
    simp [rootEvent, ParseEvent.leafValue, ParseEvent.leafVariable?, leaves]

variable [CommSemiring S]

/-- Local scalar and leaf factors can be multiplied at each selected event. -/
theorem prod_eventWeights (G : ParseGrammar R V H n) (scalar : R →+* S) (input : V → S)
    (d : Fin n) (h : H) (t : OrderedParse V H d.val) (l : ℕ) :
    ∏ e ∈ t.events l h, scalar (G.eventScalar e) * e.leafValue input =
      scalar (G.weight d h t) * (t.leaves.map input).prod := by
  rw [Finset.prod_mul_distrib, ← map_prod, prod_eventScalar G t d.isLt, prod_leafValue]

/-- Evaluating the grammar is a sum of products over canonical finite event tables. -/
theorem eval₂_eq_sum_eventWeights [Fintype V] [Fintype H] (G : ParseGrammar R V H n)
    (scalar : R →+* S) (input : V → S) (d : Fin n) (h : H) (l : ℕ) :
    eval₂Hom scalar input (G.eval d h) = ∑ t : OrderedParse V H d.val,
      ∏ e ∈ t.events l h, scalar (G.eventScalar e) * e.leafValue input := by
  rw [G.eval₂_eq_sum]
  simp only [G.prod_eventWeights]

/-- The formal state polynomial is the weighted sum of its finite event tables. -/
theorem eval_eq_sum_eventWeights [Fintype V] [Fintype H] (G : ParseGrammar R V H n)
    (d : Fin n) (h : H) (l : ℕ) :
    G.eval d h = ∑ t : OrderedParse V H d.val,
      ∏ e ∈ t.events l h, C (G.eventScalar e) * e.leafValue X := by
  rw [G.eval_eq_sum]
  simp only [G.prod_eventWeights]

/-- In the Boolean witness sum, an output variable remains formal and a witness
variable contributes its chosen bit as a field constant at each leaf. -/
theorem witnessValue_eval_eq_sum_eventWeights {F : Type*} [Field F] {X W : Type}
    [Fintype X] [Fintype W] [Fintype H] (G : ParseGrammar F (X ⊕ W) H n)
    (bits : W → Bool) (d : Fin n) (h : H) (l : ℕ) :
    witnessValue bits (G.eval d h) = ∑ t : OrderedParse (X ⊕ W) H d.val,
      ∏ e ∈ t.events l h, C (G.eventScalar e) *
        e.leafValue (Sum.elim MvPolynomial.X (fun w => C (if bits w then 1 else 0))) :=
  G.eval₂_eq_sum_eventWeights ..

end ParseGrammar

end VPVNP
end Computability
end OAI

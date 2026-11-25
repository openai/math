import OAI.ThreeFlat.Diagonal.CompressorColoring
import Mathlib.Data.Finset.Prod

namespace OAI
/-! # Greedy tag-offset selection for the two shrinking layouts -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical Pointwise
variable {V Tag : Type*} {d : ℕ} [AddCommGroup Tag]

/-- `L_x` consists of zero and the tag displacements of outgoing base arcs. -/
noncomputable def tagSteps (shift : V × Fin d → Tag) (x : V) : Finset Tag :=
  insert 0 (Finset.univ.image (fun i : Fin d => shift (x,i)))

private noncomputable def singleBad (shift : V × Fin d → Tag) (x : V) (e : V × Fin d) : Finset Tag :=
  (tagSteps shift x).image fun t => shift e + t

private noncomputable def pairBad (G : SlotGraph V d) (shift : V × Fin d → Tag)
    (e : V × Fin d) : Finset Tag :=
  ((tagSteps shift e.1) ×ˢ (tagSteps shift (G.target e).1)).image
    fun t => shift e + t.1 + t.2

private theorem tagSteps_card (shift : V × Fin d → Tag) (x : V) :
    (tagSteps shift x).card ≤ d + 1 := by
  have h := Finset.card_image_le (s := Finset.univ) (f := fun i : Fin d => shift (x,i))
  have hi := Finset.card_insert_le 0 (Finset.univ.image (fun i : Fin d => shift (x,i)))
  simpa only [Finset.card_univ, Fintype.card_fin, tagSteps] using hi.trans (Nat.add_le_add_right h 1)

private theorem pairBad_card (G : SlotGraph V d) (shift : V × Fin d → Tag) (e : V × Fin d) :
    (pairBad G shift e).card ≤ (d + 1)^2 := by
  calc
    _ ≤ ((tagSteps shift e.1) ×ˢ (tagSteps shift (G.target e).1)).card := Finset.card_image_le
    _ ≤ _ := by rw [Finset.card_product, pow_two]; exact Nat.mul_le_mul (tagSteps_card _ _) (tagSteps_card _ _)

/-- The two avoidance tests used to separate the three placed bases. The
first test is oriented at each incidence and the second is tested on arcs. -/
structure TagConditions (G : SlotGraph V d) (shift : V × Fin d → Tag) (offset : V → Tag) : Prop where
  single : ∀ x i t, t ∈ tagSteps shift x → offset x ≠ shift (incident G x i) + t
  pair : ∀ e a b, a ∈ tagSteps shift e.1 → b ∈ tagSteps shift (G.target e).1 →
    offset e.1 + offset (G.target e).1 ≠ shift e + a + b

/-- Simultaneous offsets exist at the paper's strict tag-cardinality bound.
The graph may have parallel arcs and arbitrarily many base vertices. -/
theorem exists_offsets [Fintype V] [Fintype Tag] (G : SlotGraph V d)
    (shift : V × Fin d → Tag) (size : 2*d*((d+1)+(d+1)^2) < Fintype.card Tag) :
    ∃ offset : V → Tag, TagConditions G shift offset := by
  classical
  let part (x : V) (f : V → Tag) (i : Fin d ⊕ Fin d) :=
    singleBad shift x (incident G x i) ∪
      (pairBad G shift (incident G x i)).image (fun t => t - f (adjacent G x i))
  let bad (x : V) (f : V → Tag) := Finset.univ.biUnion (part x f)
  have cardPart x f i : (part x f i).card ≤ (d+1)+(d+1)^2 := by
    exact (Finset.card_union_le ..).trans (Nat.add_le_add
      (Finset.card_image_le.trans (tagSteps_card shift x))
      (Finset.card_image_le.trans (pairBad_card G shift _)))
  have small x f : (bad x f).card < Fintype.card Tag := by
    have he := Finset.card_biUnion_le_card_mul Finset.univ (part x f) _
      (fun i _ => cardPart x f i)
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at he
    exact he.trans_lt (by simpa [two_mul] using size)
  let unary (x : V) (a : Tag) := ∀ i, a ∉ singleBad shift x (incident G x i)
  let edge (e : V × Fin d) (a b : Tag) := a+b ∉ pairBad G shift e
  obtain ⟨offset,hu,he⟩ := greedy G unary edge bad small (by
    intro x f a h
    have skip (i) : a ∉ part x f i := fun ht =>
      h (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ht⟩)
    have pair (i) : a + f (adjacent G x i) ∉ pairBad G shift (incident G x i) := by
      intro ha
      apply skip i
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨_,ha,add_sub_cancel_right ..⟩
    refine ⟨fun i ht => skip i (Finset.mem_union_left _ ht), fun i => pair (.inl i), ?_⟩
    intro i
    simpa only [edge, adjacent, incident, add_comm] using pair (.inr i))
  refine ⟨offset, ?_⟩
  constructor
  · intro x i t ht eq
    exact hu x i (Finset.mem_image.mpr ⟨t,ht,eq.symm⟩)
  · intro e a b ha hb eq
    exact he e (Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,eq.symm⟩)

end ThreeFlat.Diagonal.CompressorPacking

end OAI

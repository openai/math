import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.TourMarkerCancellation

/-! # A finite table of local options as an independent-set projection

Each row has a clique of options and a signed marker. Distinct rows may
forbid any directed pair of options. The surviving choices select one
option in every row, with exactly the weights assigned to those options.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace IndependentSetGraph

open scoped Classical BigOperators
noncomputable section

variable {I : Type*} {A : I → Type*}

abbrev ChoiceVertex (A : I → Type*) := (Σ i, A i) ⊕ I

abbrev OptionPair (conflict : (Σ i, A i) → (Σ i, A i) → Prop) :=
  {e : (Σ i, A i) × (Σ i, A i) //
    e.1 ≠ e.2 ∧ (e.1.1 = e.2.1 ∨ conflict e.1 e.2)}

abbrev ChoiceEdge (conflict : (Σ i, A i) → (Σ i, A i) → Prop) :=
  OptionPair conflict ⊕ (Σ i, A i)

variable (conflict : (Σ i, A i) → (Σ i, A i) → Prop)

def choiceLeft : ChoiceEdge conflict → ChoiceVertex A := markedLeft (fun e => e.val.1)

def choiceRight : ChoiceEdge conflict → ChoiceVertex A := markedRight (fun e => e.val.2) Sigma.fst

theorem choice_no_loops (e : ChoiceEdge conflict) : choiceLeft conflict e ≠ choiceRight conflict e := by
  cases e with
  | inl e => exact fun h => e.property.1 (Sum.inl.inj h)
  | inr _ => exact Sum.inl_ne_inr

/-- A selector specifies one option in every row. -/
def selectorBits (s : ∀ i, A i) (a : Σ i, A i) : Bool := decide (a.2 = s a.1)

@[simp] private theorem selectorBits_on (s : ∀ i, A i) (a : Σ i, A i) :
    selectorBits s a = true ↔ a.2 = s a.1 := by simp [selectorBits]

private theorem selectorBits_injective : Function.Injective (selectorBits (A := A)) := by
  intro s t h
  funext i
  have hs := (selectorBits_on s ⟨i, s i⟩).2 rfl
  rw [h] at hs
  exact (selectorBits_on t _).1 hs

def compatibleSelector (s : ∀ i, A i) : Prop :=
  ∀ i j, i ≠ j → ¬conflict ⟨i, s i⟩ ⟨j, s j⟩

private abbrev pairLeft (e : OptionPair conflict) := e.val.1
private abbrev pairRight (e : OptionPair conflict) := e.val.2

private theorem independent_selectorBits (s : ∀ i, A i) :
    independent (pairLeft conflict) (pairRight conflict) (selectorBits s) ↔ compatibleSelector conflict s := by
  constructor
  · intro hi i j hij hc
    have hne : (⟨i,s i⟩ : Sigma A) ≠ ⟨j,s j⟩ := fun h => hij (congrArg Sigma.fst h)
    exact hi ⟨(⟨i,s i⟩, ⟨j,s j⟩), hne, Or.inr hc⟩ ((selectorBits_on s ⟨i,s i⟩).2 rfl)
      ((selectorBits_on s ⟨j,s j⟩).2 rfl)
  · rintro h ⟨⟨⟨i,a⟩, ⟨j,b⟩⟩, hne, hbad⟩ ha hb
    have ha' : a = s i := (selectorBits_on s ⟨i,a⟩).1 ha
    have hb' : b = s j := (selectorBits_on s ⟨j,b⟩).1 hb
    subst a b
    have hij : i ≠ j := by rintro rfl; exact hne rfl
    exact hbad.elim hij (h i j hij)

private theorem covering_selector {x : (Σ i, A i) → Bool}
    (hi : independent (pairLeft conflict) (pairRight conflict) x)
    (hc : ∀ i, ∃ a : Sigma A, a.1 = i ∧ x a = true) :
    ∃ s, selectorBits s = x := by
  have hs (i : I) : ∃ a : A i, x ⟨i,a⟩ = true := by
    obtain ⟨⟨j,a⟩, he, hx⟩ := hc i
    cases he
    exact ⟨a,hx⟩
  choose s hs using hs
  refine ⟨s, ?_⟩
  funext a
  obtain ⟨i,a⟩ := a
  apply Bool.eq_iff_iff.mpr
  rw [selectorBits_on]
  change a = s i ↔ x ⟨i,a⟩ = true
  constructor
  · rintro rfl; exact hs i
  · intro ha
    by_contra hne
    have hne' : (⟨i,a⟩ : Sigma A) ≠ ⟨i,s i⟩ := fun h => hne (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    exact hi ⟨(⟨i,a⟩, ⟨i,s i⟩), hne', Or.inl rfl⟩ ha (hs i)

variable [Fintype I] [∀ i, Fintype (A i)]

private theorem selector_weight {R : Type*} [CommMonoid R] (s : ∀ i, A i) (w : Sigma A → R) :
    (∏ a, if selectorBits s a then w a else 1) = ∏ i, w ⟨i,s i⟩ := by
  symm
  apply Fintype.prod_of_injective (fun i => (⟨i,s i⟩ : Sigma A))
  · exact fun _ _ h => congrArg Sigma.fst h
  · rintro ⟨i,a⟩ ha
    have hne : a ≠ s i := by rintro rfl; exact ha ⟨i,rfl⟩
    simp [selectorBits, hne]
  · intro i
    simp [selectorBits]

/-- The graph projection enumerates all compatible tuples of local options. -/
theorem choice_projection {R σ : Type*} [CommRing R] (w : Sigma A → ProjectionAtom R σ) :
    project (markedProjection w) (polynomial R (choiceLeft conflict) (choiceRight conflict)) =
      ∑ s : ∀ i, A i, if compatibleSelector conflict s then
        ∏ i, atomPolynomial (w ⟨i,s i⟩) else 0 := by
  let : DecidableEq (Sigma A) := Classical.decEq _
  rw [choiceLeft, choiceRight, project_markedPolynomial]
  symm
  apply Fintype.sum_of_injective selectorBits selectorBits_injective
  · intro x hx
    split_ifs with h
    · exact (hx (covering_selector conflict h.1 h.2)).elim
    · rfl
  · intro s
    have hc (i : I) : ∃ a : Sigma A, a.1 = i ∧ selectorBits s a = true :=
      ⟨⟨i,s i⟩, rfl, (selectorBits_on s _).2 rfl⟩
    change _ = if independent (pairLeft conflict) (pairRight conflict) (selectorBits s) ∧ _ then _ else _
    simp only [hc, implies_true, and_true, independent_selectorBits, selector_weight]

theorem choice_vertex_card : Fintype.card (ChoiceVertex A) = Fintype.card (Sigma A) + Fintype.card I :=
  Fintype.card_sum

theorem choice_edge_card_le : Fintype.card (ChoiceEdge conflict) ≤
    Fintype.card (Sigma A)^2 + Fintype.card (Sigma A) := by
  have he := Fintype.card_le_of_injective (Subtype.val : OptionPair conflict → _) Subtype.val_injective
  rw [Fintype.card_sum, sq]
  exact Nat.add_le_add_right (he.trans_eq (Fintype.card_prod _ _)) _

end
end IndependentSetGraph

end SpectralBooks
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetChoices
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Polynomial-size local choices for a weighted verifier

A compatible selector takes one option in each block. Its product contains
the public input variables and the signed scalar readout of the verifier.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace IndependentSetGraph
open scoped BigOperators Classical
open Filter

structure ChoiceTable (R σ : Type*) where
  Block : Type
  Option : Block → Type
  [blockFintype : Fintype Block]
  [optionFintype : ∀ i, Fintype (Option i)]
  conflict : Sigma Option → Sigma Option → Prop
  w : Sigma Option → ProjectionAtom R σ

attribute [instance] ChoiceTable.blockFintype ChoiceTable.optionFintype

/-- Total number of local choices and their blocks. -/
def ChoiceTable.size {R σ : Type*} (t : ChoiceTable R σ) : ℕ :=
  Fintype.card t.Block + Fintype.card (Sigma t.Option)

def ChoiceTable.polynomial {R σ : Type*} [CommRing R] (t : ChoiceTable R σ) : MvPolynomial σ R :=
  ∑ s : ∀ i, t.Option i, if compatibleSelector t.conflict s then
    ∏ i, atomPolynomial (t.w ⟨i, s i⟩) else 0

/-- Local options for the family use at most polynomially many entries. -/
def HasPolynomialChoicePresentation {σ : ℕ → Type*} (R : Type*) [CommRing R]
    (f : (n : ℕ) → MvPolynomial (σ n) R) : Prop :=
  ∃ C b : ℕ, 0 < C ∧ 0 < b ∧ ∀ᶠ n : ℕ in atTop,
    ∃ t : ChoiceTable R (σ n), t.polynomial = f n ∧ t.size ≤ C * n ^ b

end IndependentSetGraph

end

end SpectralBooks
end LinearAlgebra
end OAI

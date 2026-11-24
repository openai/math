import OAI.Computability.VPVNP.MotifConversion
import OAI.Computability.VPVNP.NetworkMonomials

/-!
# Monomial witnesses for fixed-motif entries

The successful entry of a local conversion map reads one parameter label
for every repeated base block. Its exponent vector counts these labels
with multiplicity. A failed entry has an empty choice type.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifConversion

open Diagonal NetworkKernel
open scoped Classical

variable {Label : Type} [Fintype Label] {A : Type*} [CommRing A] {u : ℕ}

/-- Number of copies in which the entry reader returns a given parameter label. -/
noncomputable def entryMultiplicity (t : Fin u → Label) (l : Label) : ℕ :=
  ∑ i, if t i = l then 1 else 0

theorem labelMonomial_entryMultiplicity (κ : Label → A) (t : Fin u → Label) :
    labelMonomial κ (entryMultiplicity t) = ∏ i, κ (t i) := by
  unfold entryMultiplicity
  rw [labelMonomial_accumulate]
  apply Finset.prod_congr rfl
  intro i _
  simp [labelMonomial, apply_ite]

/-- A successful entry has one witness, including when its specialized
coefficient is zero. All witness data are determined by the label list. -/
noncomputable def entryWitness (κ : Label → A) (idx : Option (Fin u → Label)) :
    MonomialWitness κ (evalEntry κ idx) :=
  match idx with
  | none => (MonomialWitness.paths κ Empty).changeValue (by simp [evalEntry])
  | some t => (MonomialWitness.oneMonomial κ (entryMultiplicity t)).changeValue
      (labelMonomial_entryMultiplicity κ t)

@[simp] theorem entryWitness_some_exponents (κ : Label → A) (t : Fin u → Label)
    (c : (entryWitness κ (some t)).Choice) (l : Label) :
    (entryWitness κ (some t)).exponents c l = entryMultiplicity t l := rfl

/-- Each accepted entry contributes exactly one label per base repetition. -/
theorem entryWitness_totalExponent (κ : Label → A) (idx : Option (Fin u → Label))
    (c : (entryWitness κ idx).Choice) : ∑ l, (entryWitness κ idx).exponents c l = u := by
  cases idx with
  | none => exact c.elim
  | some t =>
    simp only [entryWitness_some_exponents, entryMultiplicity]
    rw [Finset.sum_comm]
    simp

end MotifConversion

end VPVNP
end Computability
end OAI

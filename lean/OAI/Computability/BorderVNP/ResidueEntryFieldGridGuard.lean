import OAI.Computability.BorderVNP.ResidueEntryVerifierCore

/-! # Binary guesses on the multiplicative grid

The raw private tape has one field-limb block per variable and one final threshold word.
Fixed query fields may be installed alongside this tape without changing its path count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryFieldGrid

open ExactQuantumFactoring BitArithmetic BooleanNetwork VPVNP
open ResidueEntryField ResidueEntryVerifierCore ResidueFourier
open scoped BigOperators Classical

variable {p s d w k b n : ℕ} {K : Type*} [Field K]

/-- Decode the complete tuple of binary field blocks and the final threshold word. -/
def choices (s d w b : ℕ) :
    (Fin (s*(d*w)+b) → Bool) ≃ ((Fin s → LimbWords d w) × Fin (2^b)) :=
  let blocks := (finProdFinEquiv.symm.arrowCongr (Equiv.refl _)).trans
    ((Equiv.curry _ _ _).trans ((Equiv.refl _).arrowCongr (limbWords d w)))
  (Fin.appendEquiv _ _).symm.trans (blocks.prodCongr ((bitsEquiv b).trans BitVec.equivFin.toEquiv))

/-- Give the grid coordinates their chart labels while retaining the same raw bit order. -/
noncomputable def namedChoices (γ : Type*) [Fintype γ] (d w b : ℕ) :
    (Fin (Fintype.card γ*(d*w)+b) → Bool) ≃ ((γ → LimbWords d w) × Fin (2^b)) :=
  (choices (Fintype.card γ) d w b).trans
    (((Fintype.equivFin γ).symm.arrowCongr (Equiv.refl _)).prodCongr (Equiv.refl _))

/-- Sum over all private binary guesses while an arbitrary larger query context is held fixed.
The wiring hypothesis only concerns the observed value on that context's installed guesses. -/
theorem sum_query_choices {γ R Q : Type*} [Fintype γ] [AddCommMonoid R]
    (install : (Fin (Fintype.card γ*(d*w)+b) → Bool) → Q) (read : Q → R)
    (f : (γ → LimbWords d w) → Fin (2^b) → R)
    (h : ∀ x, read (install x) = f (namedChoices γ d w b x).1 (namedChoices γ d w b x).2) :
    ∑ x, read (install x) = ∑ a, ∑ y, f a y := by
  calc
    _ = ∑ x, f (namedChoices γ d w b x).1 (namedChoices γ d w b x).2 :=
      Finset.sum_congr rfl fun x _ => h x
    _ = ∑ ay, f ay.1 ay.2 := (namedChoices γ d w b).sum_comp (fun ay => f ay.1 ay.2)
    _ = _ := Fintype.sum_prod_type _

/-- Inputs of the arithmetic circuit select consecutive grid words. -/
def input (b : ℕ) (i : Fin s) : BooleanNetwork (s*(d*w)+b) (d*w) :=
  select fun j => (finProdFinEquiv (i,j)).castAdd b

/-- Canonical limb words selected for a given variable. -/
theorem choices_input (x : Fin (s*(d*w)+b) → Bool) (i : Fin s) :
    (choices s d w b x).1 i = limbWords d w ((input b i).eval x) := rfl

/-- Select the final threshold word. -/
def guess (g b : ℕ) : BooleanNetwork (g+b) b := select (Fin.natAdd g)

/-- The final threshold value is the natural value of the last wires. -/
theorem choices_threshold (x : Fin (s*(d*w)+b) → Bool) :
    (choices s d w b x).2.val = value ((guess (s*(d*w)) b).eval x) := rfl

/-- Test a list of field registers for grid membership, in parallel on the query tape. -/
def gridGuard (p : ℕ) (inputs : Fin s → BooleanNetwork n (d*w)) : BooleanNetwork n 1 :=
  all (List.ofFn fun i => (inputs i).comp (validGuess d w p))

/-- Every tuple coordinate must be a canonical nonzero field element. -/
theorem gridGuard_eval (hp : p < 2^w) (inputs : Fin s → BooleanNetwork n (d*w)) (x : Fin n → Bool) :
    (gridGuard p inputs).eval x 0 = true ↔ ∀ i, validLimbs p (limbWords d w ((inputs i).eval x)) := by
  simp only [gridGuard, all_eval, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    eval_comp, validGuess_eval hp]

/-- Cost of checking all grid fields, including materialization of the input words. -/
theorem gridGuard_count (inputs : Fin s → BooleanNetwork n (d*w)) (c : ℕ)
    (hc : ∀ i, (inputs i).net.count ≤ c) :
    (gridGuard p inputs).net.count ≤ s*(c + (d*(49*w+9) + d*(49*w+12) + 3) + 1) + 1 := by
  have hh := all_count (List.ofFn fun i => (inputs i).comp (validGuess d w p))
    (c := c + (d*(49*w+9) + d*(49*w+12) + 3)) (by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      rw [count_comp]
      exact Nat.add_le_add (hc _) (validGuess_count ..))
  simpa only [gridGuard, List.length_ofFn] using hh

end ResidueEntryFieldGrid

end BorderVNP
end Computability
end OAI

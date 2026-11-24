import OAI.Computability.VPVNP.Circuits
import OAI.Computability.VPVNP.PairedFamily
import OAI.Computability.VPVNP.Hamiltonian
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Pinning the program bits

In §1.1 of *VP and VNP differ over every field*, a fixed prefix selects a
program, and the remaining bits encode a directed graph. Pinning a prefix
removes every monomial belonging to a different program. The Hamiltonian
cycle projection follows whenever the selected program counts each spanning
cycle once and rejects all other adjacency matrices within the clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped BigOperators
open MvPolynomial

section

variable {E R : Type*} [CommSemiring R] {p k : ℕ}

/-- The projection pins the prefix. Each suffix bit selects either one or its edge variable. -/
def pinVariables (bits : Fin p → Bool) (edge : Fin k ≃ E) : Projection R (Fin (p + k) × Bool) E :=
  fun v => Fin.append (fun i ↦ Sum.inr (if v.2 = bits i then 1 else 0))
    (fun j ↦ if v.2 then Sum.inl (edge j) else Sum.inr 1) v.1

private def appendEdgeBits (edge : Fin k ≃ E) :
    ((Fin p → Bool) × (E → Bool)) ≃ (Fin (p + k) → Bool) where
  toFun w := Fin.append w.1 (w.2 ∘ edge)
  invFun w := (w ∘ Fin.castAdd k, fun e ↦ w (Fin.natAdd p (edge.symm e)))
  left_inv := by
    intro w
    ext i <;> simp [Function.comp_def]
  right_inv := by
    intro w
    simpa [Function.comp_def] using (Fin.append_castAdd_natAdd (f := w))

private theorem pinVariables_product [Fintype E] (bits actual : Fin p → Bool)
    (edge : Fin k ≃ E) (x : E → Bool) :
    (∏ j, (pinVariables (R := R) bits edge (j, Fin.append actual (x ∘ edge) j)).elim X C) =
      if actual = bits then ∏ e, if x e then X e else 1 else 0 := by
  rw [Fin.prod_univ_add]
  simp only [pinVariables, Fin.append_left, Fin.append_right, Function.comp_apply,
    Sum.elim_inr, apply_ite C, map_one, map_zero,
    apply_ite (fun z : E ⊕ R => z.elim X C), Sum.elim_inl]
  simp only [Fintype.prod_boole, ← funext_iff]
  split_ifs
  · simpa using edge.prod_comp (fun e ↦ (if x e then X e else 1 : MvPolynomial E R))
  · exact zero_mul _

/-- The coefficient hypothesis concerns only words beginning with the chosen prefix. -/
theorem pairedPolynomial_pin [Fintype E] [DecidableEq E] (bits : Fin p → Bool)
    (edge : Fin k ≃ E) (u : (Fin (p + k) → Bool) → R) (w : (E → Bool) → R)
    (agree : ∀ x, u (Fin.append bits (x ∘ edge)) = w x) :
    (pinVariables bits edge).hom (pairedPolynomial u) = booleanPolynomial w := by
  classical
  simp only [Projection.hom, pairedPolynomial, map_sum, map_mul, eval₂Hom_C, map_prod, eval₂Hom_X']
  rw [← (appendEdgeBits (p := p) edge).sum_comp, Fintype.sum_prod_type]
  change (∑ a : Fin p → Bool, ∑ x : E → Bool, C (u (Fin.append a (x ∘ edge))) *
    ∏ j, (pinVariables bits edge (j, Fin.append a (x ∘ edge) j)).elim X C) = _
  simp only [pinVariables_product]
  rw [Finset.sum_eq_single bits]
  · simp [booleanPolynomial, agree]
  · intro a _ ha
    simp [ha]
  · simp

/-- Pinning a prefix whose coefficients recognize Hamiltonian adjacency matrices
projects the family member at length `p + m * m` to the directed cycle polynomial. -/
theorem pairedPolynomial_pin_hamiltonian (bits : Fin p → Bool) (m : ℕ)
    (u : (Fin (p + m * m) → Bool) → R)
    (agree : ∀ x : Fin m × Fin m → Bool,
      u (Fin.append bits (x ∘ finProdFinEquiv.symm)) = cycleIndicator R m x) :
    (pinVariables bits finProdFinEquiv.symm).hom (pairedPolynomial u) =
      hamiltonianCyclePolynomial R m :=
  (pairedPolynomial_pin bits finProdFinEquiv.symm u (cycleIndicator R m) agree).trans
    (booleanPolynomial_cycleIndicator R m)

/-- The selected integer counts may be recognized before base change to the field. -/
theorem P_pin_hamiltonian {p : ℕ} (bits : Fin p → Bool) (m : ℕ)
    (agree : ∀ x : Fin m × Fin m → Bool,
      acceptingCount (Fin.append bits (x ∘ finProdFinEquiv.symm)) = cycleIndicator ℕ m x)
    (S : Type*) [CommRing S] :
    (pinVariables bits finProdFinEquiv.symm).hom
      (MvPolynomial.map (Int.castRingHom S) (P (p + m * m))) =
      hamiltonianCyclePolynomial S m := by
  rw [map_P]
  apply pairedPolynomial_pin_hamiltonian
  intro x
  rw [agree]
  classical
  simp [cycleIndicator, Nat.cast_ite]

end

end VPVNP
end Computability
end OAI

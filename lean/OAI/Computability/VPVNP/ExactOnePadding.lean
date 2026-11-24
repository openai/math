import OAI.Computability.VPVNP.ExactOneWeights

/-!
# A dummy variable for exact-one instances

The Hamiltonian graph needs at least one variable track. Adding a final variable
and a singleton negative clause gives each old assignment a unique extension
with the same weight, including when the original instance has no variables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF MvPolynomial
open scoped Classical

variable {k : ℕ} {R τ : Type*}

/-- Embed the old variables as the initial coordinates and force the final one to false. -/
def pad (φ : CNF k) : CNF (k + 1) :=
  [(Fin.last k, false)] :: φ.map (List.map fun l => (l.1.castSucc, l.2))

/-- The forced coordinate carries the unit label. -/
def padProjection [One R] (w : Projection R (Fin k) τ) : Projection R (Fin (k + 1)) τ :=
  Fin.snoc (α := fun _ => τ ⊕ R) w (.inr 1)

@[simp] theorem length_pad (φ : CNF k) : (pad φ).length = φ.length + 1 := by simp [pad]

@[simp] theorem literalCount_pad (φ : CNF k) : literalCount (pad φ) = literalCount φ + 1 := by
  simp [pad, literalCount, List.map_map, Function.comp_def, Nat.add_comm]

/-- The old coordinates retain all the old constraints. -/
theorem holds_pad_iff (φ : CNF k) (x : Fin (k + 1) → Bool) :
    Holds (pad φ) x ↔ x (Fin.last k) = false ∧ Holds φ (fun i => x i.castSucc) := by
  cases hx : x (Fin.last k) <;>
    simp [Holds, pad, List.countP_map, Function.comp_def, hx]

/-- The added variable has weight one in every satisfying product because it is forced false. -/
theorem weightedExactOne_pad [CommSemiring R] (φ : CNF k) (w : Fin (k + 1) → R) :
    weightedExactOne (pad φ) w = weightedExactOne φ (fun i => w i.castSucc) := by
  let e := Fin.snocEquiv (n := k) (fun _ => Bool)
  unfold weightedExactOne
  rw [← e.sum_comp (fun x => if Holds (pad φ) x then ∏ i, if x i then w i else 1 else 0),
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [holds_pad_iff, e, Fin.snocEquiv_apply, Fin.snoc_last, Fin.snoc_castSucc,
    Bool.true_eq_false, false_and, ite_false, Finset.sum_const_zero, zero_add, true_and]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Holds φ x
  · simp [hx, Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc]
  · simp [hx]

/-- Variable-or-constant labels of the original exact-one polynomial lift to the padded graph. -/
theorem weightedExactOne_padProjection [CommSemiring R] (φ : CNF k) (w : Projection R (Fin k) τ) :
    weightedExactOne (pad φ) (fun i => (padProjection w i).elim X C) =
      weightedExactOne φ (fun i => (w i).elim X C) := by
  simp [weightedExactOne_pad, padProjection]

end ExactOne

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.LeafBijection
import OAI.Computability.VPVNP.ParseGrammar
import OAI.Computability.VPVNP.PairedFamily
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Perm

/-!
# Querying a grammar coefficient by leaf assignments

In equation (8.1) of *VP and VNP differ over every field*, the queried monomial
contains one distinct variable for each bit position. Its coefficient is the sum of
the parse weights, counting each bijective assignment of terminal occurrences to
matching query positions once.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

open MvPolynomial
variable {V R H : Type*} {n m : ℕ} [CommSemiring R]

/-- A list of terminals contributes one copy of each listed variable. -/
theorem list_prod_X_eq_monomial (l : List V) :
    (l.map (X (R := R))).prod =
      monomial ((l.map (fun v ↦ Finsupp.single v 1)).sum) 1 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, X, monomial_mul_monomial, one_mul]

private theorem terminalExponents_eq_multiset [DecidableEq V] (l : List V) :
    (l.map (fun v ↦ Finsupp.single v (1 : ℕ))).sum = (l : Multiset V).toFinsupp := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← Multiset.toFinsupp_singleton, ← map_add]
    rfl

/-- The terminal exponent vector matches the queried monomial exactly when the two
words have the same multiset of variables. -/
theorem terminalExponents_eq_query_iff (l : List V) (q : Fin m → V) :
    (l.map (fun v ↦ Finsupp.single v (1 : ℕ))).sum = ∑ i, Finsupp.single (q i) 1 ↔
      (l : Multiset V) = (List.ofFn q : Multiset V) := by
  classical
  have he : ∑ i, Finsupp.single (q i) 1 =
      ((List.ofFn q).map (fun v ↦ Finsupp.single v (1 : ℕ))).sum := by
    simp [List.map_ofFn, List.sum_ofFn, Function.comp_def]
  rw [he]
  rw [terminalExponents_eq_multiset, terminalExponents_eq_multiset]
  exact Multiset.toFinsupp.injective.eq_iff

variable [Fintype V] [Fintype H]
open scoped Classical

/-- Extract the coefficient by comparing multisets of terminal variables. -/
theorem coeff_eval_query_multiset (G : ParseGrammar R V H n) (d : Fin n) (h : H)
    (q : Fin m → V) :
    (G.eval d h).coeff (∑ i, Finsupp.single (q i) 1) =
      ∑ p : OrderedParse V H d.val,
        if (p.leaves : Multiset V) = (List.ofFn q : Multiset V) then G.weight d h p else 0 := by
  rw [G.eval_eq_sum, coeff_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [list_prod_X_eq_monomial, C_mul_monomial, coeff_monomial]
  simp [terminalExponents_eq_query_iff]

/-- For an injective query this coefficient counts one weight for each parse and each
bijective, label-preserving assignment of its leaves to the queried positions. -/
theorem coeff_eval_query_bijections (G : ParseGrammar R V H n) (d : Fin n) (h : H)
    (q : Fin m → V) (hq : Function.Injective q) :
    (G.eval d h).coeff (∑ i, Finsupp.single (q i) 1) =
      ∑ p : OrderedParse V H d.val, ∑ _ : LeafBijection p.leaves q, G.weight d h p := by
  rw [G.coeff_eval_query_multiset]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  let := LeafBijection.subsingleton_of_injective p.leaves hq
  by_cases hmatch : (p.leaves : Multiset V) = (List.ofFn q : Multiset V)
  · obtain ⟨e⟩ := (LeafBijection.nonempty_iff _ _).mpr hmatch
    let : Unique (LeafBijection p.leaves q) := ⟨⟨e⟩, fun _ ↦ Subsingleton.elim _ _⟩
    simp [hmatch]
  · have : IsEmpty (LeafBijection p.leaves q) :=
      not_nonempty_iff.mp (fun he ↦ hmatch ((LeafBijection.nonempty_iff _ _).mp he))
    simp [hmatch]

/-- The query of (8.1) pairs the position index with the requested bit.
Distinct first coordinates make the query injective over every coefficient semiring. -/
theorem coeff_eval_paired_bijections (G : ParseGrammar R (Fin m × Bool) H n)
    (d : Fin n) (h : H) (x : Fin m → Bool) :
    (G.eval d h).coeff (pairedExponent x) =
      ∑ p : OrderedParse (Fin m × Bool) H d.val,
        ∑ _ : LeafBijection p.leaves (fun i ↦ (i, x i)), G.weight d h p := by
  refine (G.coeff_eval_query_bijections d h (fun i ↦ (i, x i)) fun _ _ e ↦
    congrArg Prod.fst e).trans ?_
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext
  simp

end ParseGrammar

end VPVNP
end Computability
end OAI

import OAI.Hierarchy.GraphVNPPolynomial
import OAI.Computability.VPVNP.PolynomialBounds
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Gate count for the Boolean witness of a graph contraction

A local table has one term for each assignment to the incident edges.
Each such term tests the full label vector on those edges. -/

namespace Hierarchy

open Computability.VPVNP MvPolynomial
open scoped Classical

private theorem size_sum {J σ F : Type*} [Field F] (s : Finset J)
    (p : J → MvPolynomial σ F) (k : ℕ) (h : ∀ i, circuitSize (p i) ≤ k) :
    circuitSize (∑ i ∈ s, p i) ≤ s.card * (k+1) := by
  induction s using Finset.induction_on with
  | empty => simpa using (circuitSize_C (σ := σ) (0 : F)).le
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul]
    exact (circuitSize_binOp_le .add ..).trans (by have := h i; omega)

private theorem size_product {J σ F : Type*} [Field F] (s : Finset J)
    (p : J → MvPolynomial σ F) (k : ℕ) (h : ∀ i, circuitSize (p i) ≤ k) :
    circuitSize (∏ i ∈ s, p i) ≤ s.card * (k+1) := by
  induction s using Finset.induction_on with
  | empty => simpa using (circuitSize_C (σ := σ) (1 : F)).le
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul]
    exact (circuitSize_binOp_le .mul ..).trans (by have := h i; omega)

namespace IncidenceGraph

variable (G : IncidenceGraph) (F : Type*) [Field F] (q : ℕ)

private theorem size_factor (e : G.E) (a i : Fin q) :
    circuitSize (G.labelFactor F q e a i) ≤ 1 := by
  unfold labelFactor
  split
  · simp
  · have one : circuitSize (1 : MvPolynomial (G.TableVar q ⊕ G.Witness q) F) = 0 := by
      simpa using circuitSize_C (σ := G.TableVar q ⊕ G.Witness q) (1 : F)
    simpa only [BinOp.apply, one, circuitSize_X, Nat.zero_add] using
      circuitSize_binOp_le .sub (1 : MvPolynomial (G.TableVar q ⊕ G.Witness q) F) (X (Sum.inr (e,i)))

private theorem size_selector (e : G.E) (a : Fin q) :
    circuitSize (G.labelSelector F q e a) ≤ q*2 := by
  simpa only [labelSelector, Finset.card_univ, Fintype.card_fin] using
    size_product Finset.univ _ 1 (G.size_factor F q e a)

/-- Counting binary gates in the product of local table polynomials. -/
theorem circuitSize_witnessPolynomial_le (b : ℕ) (hq : 0 < q) (deg : ∀ v, G.degree v ≤ b) :
    circuitSize (G.witnessPolynomial F q) ≤
      Fintype.card G.V * (q ^ b * (b*(q*2+1)+2)+1) := by
  have term (v : G.V) (t : G.Incident v → Fin q) :
      circuitSize (G.tableTerm F q v t) ≤ b*(q*2+1)+1 := by
    have selectors := size_product Finset.univ _ (q*2)
      (fun e : G.Incident v => G.size_selector F q e.val (t e))
    rw [Finset.card_univ] at selectors
    have cap := selectors.trans (Nat.mul_le_mul_right _ (deg v))
    have gate := circuitSize_binOp_le .mul
      (X (σ := G.TableVar q ⊕ G.Witness q) (Sum.inl ⟨v,t⟩))
      (∏ e : G.Incident v, G.labelSelector F q e.val (t e))
    rw [circuitSize_X, zero_add] at gate
    exact gate.trans (Nat.add_le_add_right cap 1)
  have row (v : G.V) : circuitSize (G.tablePolynomial F q v) ≤ q^b*(b*(q*2+1)+2) := by
    have locals := size_sum Finset.univ _ _ (term v)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at locals
    exact locals.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq (deg v)))
  exact size_product Finset.univ _ _ row

end IncidenceGraph

theorem witnessPolynomial_size_polynomial (F : Type*) [Field F] (G : ℕ → IncidenceGraph)
    (order : PolynomiallyBounded (fun n => Fintype.card (G n).V))
    (degree : ∃ b, ∀ n (v : (G n).V), (G n).degree v ≤ b) :
    PolynomiallyBounded (fun n => circuitSize ((G n).witnessPolynomial F n)) := by
  obtain ⟨b, hb⟩ := degree
  apply (order.mul (((PolynomiallyBounded.id.pow b).mul
    (((PolynomiallyBounded.const b).mul ((PolynomiallyBounded.id.mul
      (PolynomiallyBounded.const 2)).add (PolynomiallyBounded.const 1))).add
        (PolynomiallyBounded.const 2))).add (PolynomiallyBounded.const 1))).of_eventually_le 1
  intro n hn
  exact (G n).circuitSize_witnessPolynomial_le F n b hn (hb n)


end Hierarchy

end OAI

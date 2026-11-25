import OAI.Computability.MultitapeWeakETH.FieldTables
import Mathlib.LinearAlgebra.Lagrange

/-! # Coherent pin choices and coefficient extraction -/

namespace OAI.Computability.MultitapeWeakETH

open Finset Polynomial
open scoped BigOperators Polynomial

/-- Contracting a root table that sends one pin to each vertex gives the
prescribed sum of the pinned contractions. Repeated pin tuples are allowed. -/
theorem contract_root_pins {K I V : Type*} [CommSemiring K] [Fintype I] [Fintype V] [DecidableEq V]
    {Pin : V → Type*} [∀ v, Fintype (Pin v)] [∀ v, DecidableEq (Pin v)]
    (pins : I → (v : V) → Pin v) (weight : I → K) (value : ((v : V) → Pin v) → K) :
    ∑ q, (∑ i, if pins i = q then weight i else 0) * value q =
      ∑ i, weight i * value (pins i) := by
  simp_rw [sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  simp

/-- One root table displays the sum of all the specified basis vectors once
the pinned outputs have singleton support. The root cancels the nonzero
scalar for each selected stream. -/
theorem coherent_display {K I V B : Type*} [Field K] [Fintype I] [Fintype V] [DecidableEq V] [DecidableEq B]
    {Pin : V → Type*} [∀ v, Fintype (Pin v)] [∀ v, DecidableEq (Pin v)]
    (pins : I → (v : V) → Pin v) (display : I → B)
    (output : ((v : V) → Pin v) → B → K) (scalar : I → K) (nz : ∀ i, scalar i ≠ 0)
    (basis : ∀ i b, output (pins i) b = if display i = b then scalar i else 0) :
    ∃ root : ((v : V) → Pin v) → K, ∀ b,
      ∑ q, root q * output q b = ∑ i, if display i = b then (1:K) else 0 := by
  refine ⟨fun q => ∑ i, if pins i = q then (scalar i)⁻¹ else 0,fun b => ?_⟩
  rw [contract_root_pins pins (fun i => (scalar i)⁻¹) (fun q => output q b)]
  exact sum_congr rfl fun i _ => by by_cases equal : display i = b <;> simp [basis,equal,nz]

/-- One set of D+1 nodes and weights extracts a specified coefficient from
every bounded-degree polynomial over an infinite field, including fields of
positive characteristic. -/
theorem coefficient_from_evaluations {K : Type*} [Field K] [Infinite K] (D A : ℕ) :
    ∃ (node : Fin (D+1) ↪ K) (weight : Fin (D+1) → K),
      ∀ f : K[X], f.natDegree ≤ D → f.coeff A = ∑ i, weight i * f.eval (node i) := by
  classical
  let node : Fin (D+1) ↪ K := (Fin.valEmbedding).trans (Infinite.natEmbedding K)
  refine ⟨node,fun i => (Lagrange.basis univ node i).coeff A,fun f hf => ?_⟩
  have degree : f.degree < (univ : Finset (Fin (D+1))).card := by
    simp only [card_univ,Fintype.card_fin]
    exact f.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hf)
  have interp := congrArg (fun g : K[X] => g.coeff A)
    (Lagrange.eq_interpolate (v := ⇑node) node.injective.injOn degree)
  simpa only [Lagrange.interpolate_apply,finsetSum_coeff,coeff_C_mul,coeff_mul_C,mul_comm] using interp

/-- Applying the evaluations at each local table commutes with the finite
wire-label contraction. The same weights work for every external setting. -/
theorem Network.extract_coefficient {n b : ℕ} (G : Network n b) {K : Type*} [Field K] [Infinite K]
    (D A : ℕ) (table : (v : Fin G.vertices) → G.View v → K[X])
    (bounded : ∀ x z, (G.contract table x z).natDegree ≤ D) :
    ∃ (node : Fin (D+1) ↪ K) (weight : Fin (D+1) → K), ∀ x z,
      (G.contract table x z).coeff A = ∑ i, weight i *
        G.contract (fun v t => (table v t).eval (node i)) x z := by
  obtain ⟨node,weight,extract⟩ := coefficient_from_evaluations (K := K) D A
  refine ⟨node,weight,fun x z => ?_⟩
  rw [extract _ (bounded x z)]
  apply sum_congr rfl
  intro i _
  simp [Network.contract,eval_finsetSum,eval_prod]

end OAI.Computability.MultitapeWeakETH

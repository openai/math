import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Taylor coefficients of rational tensor powers

Interpolate the polynomial numerators away from the zeros of their common
denominator. The Lagrange basis then gives one set of scalar weights for
every entry of a tensor power, using one more node than its numerator degree.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators
open Polynomial

section

variable {K : Type*} [Field K] [Infinite K]

private theorem exists_regularNodes (h : K[X]) (h0 : h.coeff 0 ≠ 0) (n : ℕ) :
    ∃ t : Fin (n + 1) ↪ K, ∀ j, h.eval (t j) ≠ 0 := by
  classical
  have hn : h ≠ 0 := fun e => h0 (by simp [e])
  let roots : Finset K := h.roots.toFinset
  let good := (roots : Set K)ᶜ
  let : Infinite good := (roots.finite_toSet.infinite_compl).to_subtype
  let xs : Fin (n + 1) ↪ good := Fin.valEmbedding.trans (Infinite.natEmbedding good)
  refine ⟨xs.trans (Function.Embedding.subtype _), ?_⟩
  intro j hj
  apply (xs j).property
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hn).mpr hj)

omit [Infinite K] in
private theorem exists_weights_at_nodes (h : K[X]) {n : ℕ} (t : Fin (n + 1) ↪ K)
    (ht : ∀ j, h.eval (t j) ≠ 0) :
    ∃ a : ℕ → Fin (n + 1) → K, ∀ p : K[X], p.natDegree ≤ n → ∀ i,
      PowerSeries.coeff i ((p : PowerSeries K) * (h : PowerSeries K)⁻¹) =
        ∑ j, a i j * (p.eval (t j) / h.eval (t j)) := by
  classical
  let b := Lagrange.basis Finset.univ t
  refine ⟨fun i j => h.eval (t j) *
    PowerSeries.coeff i ((b j : PowerSeries K) * (h : PowerSeries K)⁻¹), ?_⟩
  intro p hp i
  have hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact p.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hp))
  have hi := Lagrange.eq_interpolate t.injective.injOn hd
  rw [Lagrange.interpolate_apply] at hi
  change PowerSeries.coeff i (Polynomial.coeToPowerSeries.ringHom p * _) = _
  conv_lhs => rw [hi, map_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, mul_assoc,
    PowerSeries.coeff_C_mul]
  dsimp [b]
  field_simp [ht]

/-- Uniform interpolation of all Taylor coefficients of all rational functions
with a fixed regular denominator and a specified bound on the numerator degree. -/
theorem exists_rationalCoefficient_weights (h : K[X]) (h0 : h.coeff 0 ≠ 0) (n : ℕ) :
    ∃ t : Fin (n + 1) ↪ K, (∀ j, h.eval (t j) ≠ 0) ∧
      ∃ a : ℕ → Fin (n + 1) → K, ∀ p : K[X], p.natDegree ≤ n → ∀ i,
        PowerSeries.coeff i ((p : PowerSeries K) * (h : PowerSeries K)⁻¹) =
          ∑ j, a i j * (p.eval (t j) / h.eval (t j)) := by
  obtain ⟨t, ht⟩ := exists_regularNodes h h0 n
  exact ⟨t, ht, exists_weights_at_nodes h t ht⟩

/-- Each coefficient of the tensor power is a linear combination of just
`e * k + 1` evaluated powers. The same weights work for all matrix entries
when the index type is the product of output and input indices. -/
theorem exists_rationalPowerCoefficient_weights {ι : Type*} (h : K[X]) (h0 : h.coeff 0 ≠ 0)
    (p : ι → K[X]) (e : ℕ) (hp : ∀ z, (p z).natDegree ≤ e) (k : ℕ) :
    ∃ t : Fin (e * k + 1) ↪ K, (∀ j, h.eval (t j) ≠ 0) ∧
      ∃ a : ℕ → Fin (e * k + 1) → K, ∀ (i : ℕ) (x : Fin k → ι),
        PowerSeries.coeff i (∏ r, ((p (x r) : PowerSeries K) * (h : PowerSeries K)⁻¹)) =
          ∑ j, a i j * ∏ r, ((p (x r)).eval (t j) / h.eval (t j)) := by
  classical
  obtain ⟨t, ht⟩ := exists_regularNodes h h0 (e * k)
  obtain ⟨a, ha⟩ := exists_weights_at_nodes (h ^ k) t
    (fun j => by simpa only [Polynomial.eval_pow] using pow_ne_zero k (ht j))
  refine ⟨t, ht, a, ?_⟩
  intro i x
  let q := ∏ r, p (x r)
  have hq : q.natDegree ≤ e * k := calc
    q.natDegree ≤ ∑ r, (p (x r)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _ : Fin k, e := Finset.sum_le_sum fun r _ => hp (x r)
    _ = e * k := by simp [Nat.mul_comm]
  specialize ha q hq i
  have hpow : (q : PowerSeries K) = ∏ r, (p (x r) : PowerSeries K) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := K)) _ _
  simpa only [hpow, Polynomial.coe_pow, ← PowerSeries.inv_pow, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, q, Polynomial.eval_prod,
    Polynomial.eval_pow, Finset.prod_div_distrib] using ha

end

end FiniteFourier
end LinearAlgebra
end OAI

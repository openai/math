import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchyEntropy
import OAI.Combinatorics.RamseyFive.Entropy.EntropyCrossEntropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # Charging blockwise error masks by their marginal entropies -/

namespace OAI.Computability.MultitapeWeakETH

open MatrixMultiplication.Foundation Finset
open scoped Classical BigOperators

private def asLaw {A : Type*} [Fintype A] (p : FiniteLaw A) : SharpRamseyFive.FiniteEntropy.Law A :=
  ⟨p.mass,p.nonneg,p.total⟩

private theorem block_entropy {A : Type*} [Fintype A] (p : FiniteLaw A) (w : ℕ)
    (mask : A → Fin w → Bool) {e : ℝ} (he : 0 < e) (hsmall : e ≤ 1/2) :
    finiteEntropy ((p.map mask).mass) ≤
      ∑ a, p.mass a * (-(w:ℝ)*Real.log (1-e) +
        ((univ.filter fun i => mask a i).card : ℝ)*(Real.log (1-e)-Real.log e)) := by
  let prob (b : Bool) := if b then e else 1-e
  let q (x : Fin w → Bool) := ∏ i, prob (x i)
  have positive (b : Bool) : 0 < prob b := by cases b <;> simp [prob] <;> linarith
  have total : ∑ x, q x = 1 := by
    change (∑ x : Fin w → Bool, ∏ i, prob (x i)) = 1
    rw [← Fintype.prod_sum]
    simp [prob]
  let m := SharpRamseyFive.FiniteEntropy.map (asLaw p) mask
  have cross := SharpRamseyFive.FiniteEntropy.entropy_le_cross_entropy m q
    (fun x => (prod_pos fun i _ => positive (x i)).le) total.le
    (fun x _ => prod_pos fun i _ => positive (x i))
  have agrees : finiteEntropy (p.map mask).mass = SharpRamseyFive.FiniteEntropy.entropy m := by
    simp only [finiteEntropy,entropyTerm,SharpRamseyFive.FiniteEntropy.entropy,← sum_neg_distrib,
      neg_mul]
    rfl
  rw [agrees]
  apply cross.trans_eq
  rw [SharpRamseyFive.FiniteEntropy.sum_map]
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro a _
  have point (i : Fin w) : Real.log (prob (mask a i)) =
      Real.log (1-e) + (if mask a i then Real.log e-Real.log (1-e) else 0) := by
    cases h : mask a i <;> simp [prob]
  change -(p.mass a*Real.log (∏ i, prob (mask a i))) = _
  rw [Real.log_prod (fun i _ => (positive (mask a i)).ne')]
  simp only [point,sum_add_distrib,sum_ite,sum_const_zero,add_zero,sum_const,card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  ring

/-- If all masks together have weight at most en, their block marginal
entropies cost at most n times the binary entropy in natural logarithms. The
blocks can have different widths and arbitrary dependencies. -/
theorem mask_entropy {A V : Type*} [Fintype A] [Fintype V] (p : FiniteLaw A)
    (width : V → ℕ) (mask : (v : V) → A → Fin (width v) → Bool)
    {e : ℝ} (he : 0 < e) (hsmall : e ≤ 1/2)
    (weight : ∀ a, (∑ v, ((univ.filter fun i => mask v a i).card : ℝ)) ≤ e * ∑ v, (width v:ℝ)) :
    ∑ v, finiteEntropy ((p.map (mask v)).mass) ≤ (∑ v, (width v:ℝ))*Real.binEntropy e := by
  let g := Real.log (1-e)-Real.log e
  have hg : 0 ≤ g := sub_nonneg.mpr (Real.log_le_log he (by linarith))
  apply (sum_le_sum (s := univ) (fun v _ => block_entropy p _ (mask v) he hsmall)).trans
  rw [sum_comm]
  calc
    _ ≤ ∑ a, p.mass a * ((∑ v, (width v:ℝ))*Real.binEntropy e) := by
      apply sum_le_sum
      intro a _
      rw [← mul_sum,sum_add_distrib,← sum_mul,← sum_mul,sum_neg_distrib]
      apply mul_le_mul_of_nonneg_left _ (p.nonneg a)
      have h := mul_le_mul_of_nonneg_right (weight a) hg
      simp only [g] at h
      rw [Real.binEntropy,Real.log_inv,Real.log_inv]
      nlinarith only [h]
    _ = _ := by rw [← sum_mul,p.total,one_mul]

end OAI.Computability.MultitapeWeakETH

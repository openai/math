import OAI.LinearAlgebra.FiniteFourier.ConvolutionEnvelope
import OAI.LinearAlgebra.FiniteFourier.ConvolutionPrimes

/-! # Cost of the three open products at each split jet point

The common packing map is used twice. The return map combines the three
products and reduces each of the surviving rows modulo the fixed monic
power-basis relation. Only those reductions use fixed convolutions.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace JetAssembly

/-- Cost of the two packing maps and the return map for one split point of
power-basis degree `e` and jet height `h`. -/
noncomputable def blockCost (e h : ℕ) : ℕ :=
  2 * (2 * e * h) + (3 * (2 * (2 * e * h) - 1) +
    h * (6 * (2 * integralConvolutionCost e + e) + 2 * e))

/-- Charge the fixed row products to the shorter-length envelope. -/
theorem blockCost_le {e s : ℕ} (he : 0 < e) (hes : e ≤ s) (h : ℕ) :
    (blockCost e h : ℝ) ≤ 36 * (e : ℝ) * h * convolutionEnvelope s := by
  have hsize : blockCost e h ≤ 24 * e * h + 12 * integralConvolutionCost e * h := calc
    _ ≤ 2 * (2 * e * h) + (3 * (2 * (2 * e * h)) +
        h * (6 * (2 * integralConvolutionCost e + e) + 2 * e)) := by
      unfold blockCost
      gcongr
      exact Nat.sub_le _ _
    _ = _ := by ring
  have hb : (blockCost e h : ℝ) ≤ 24 * e * h + 12 * integralConvolutionCost e * h := by
    exact_mod_cast hsize
  have he' : 0 < (e : ℝ) := by exact_mod_cast he
  have hd : (integralConvolutionCost e : ℝ) ≤ convolutionEnvelope s * e :=
    (div_le_iff₀ he').mp (convolutionRate_le_envelope he hes)
  have hE := convolutionEnvelope_one_le (he.trans_le hes)
  have h₁ := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (α := ℝ) h)
  have h₂ := mul_le_mul_of_nonneg_right hE (mul_nonneg he'.le (Nat.cast_nonneg (α := ℝ) h))
  linarith only [hb, h₁, h₂]

/-- A scalar branch and a branch of width `Fintype.card (X i)` on each
axis give this many split points in all summands combined. The local address
type can be a single frequency or a quadratic coordinate and a frequency. -/
theorem card_splitPoints {ι : Type*} [DecidableEq ι] (axes : Finset ι)
    (X : ι → Type*) [∀ i, Fintype (X i)] :
    Fintype.card (Σ I : axes.powerset, (i : I.val) → X i) =
      ∏ i ∈ axes, (Fintype.card (X i) + 1) := by
  classical
  rw [Finset.prod_add_one, Fintype.card_sigma]
  simp only [Fintype.card_pi, Finset.univ_eq_attach]
  rw [← Finset.sum_attach axes.powerset (fun t => ∏ i ∈ t, Fintype.card (X i))]
  exact Finset.sum_congr rfl fun t _ =>
    Finset.prod_attach t.val (fun i => Fintype.card (X i))

variable {B : Type*} [Fintype B]

/-- Each split point gives three equal-length convolution gates. -/
theorem sum_childLength (e h : B → ℕ) :
    (∑ i : B × Fin 3, 2 * e i.1 * h i.1) = 6 * ∑ b, e b * h b := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp
  ring

/-- For a family of split points, the ancillary linear work is at most six
times the total length of the three children per point times the envelope. -/
theorem sum_blockCost_le {s : ℕ} (e h : B → ℕ)
    (he : ∀ b, 0 < e b) (hes : ∀ b, e b ≤ s) :
    ((∑ b, blockCost (e b) (h b) : ℕ) : ℝ) ≤
      6 * ((∑ i : B × Fin 3, 2 * e i.1 * h i.1 : ℕ) : ℝ) * convolutionEnvelope s := by
  rw [sum_childLength]
  push_cast
  calc
    _ ≤ ∑ b, 36 * (e b : ℝ) * h b * convolutionEnvelope s :=
      Finset.sum_le_sum fun b _ => blockCost_le (he b) (hes b) _
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- For the list protecting two take `k = 4`, and for a dyadic list take
`k = 3`. The number of points is the product of the selected prime widths. -/
theorem sum_childLength_le_of_packing {P : Finset ℕ} {n e : ℕ} {cut : ℝ}
    (pack : PrimeJetPacking P n e cut)
    (hcard : Fintype.card B = ∏ p ∈ pack.axes, p) (h : B → ℕ)
    {k : ℕ} (hh : ∀ b, h b ≤ k * pack.jet) :
    (∑ i : B × Fin 3, 2 * e * h i.1) ≤ 3 * (2*k) * (9*n) := by
  calc
    _ = 6 * ∑ b, e * h b := sum_childLength (fun _ : B => e) h
    _ ≤ 6 * ∑ _ : B, e * (k * pack.jet) := by gcongr with b; exact hh b
    _ = 3 * (2*k) * ((∏ p ∈ pack.axes, p) * e * pack.jet) := by
      simp [hcard]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ pack.volume_upper

/-- Normalized linear overhead for all split products on one packed list. -/
theorem sum_blockCost_div_le_of_packing {P : Finset ℕ} {n e s : ℕ} {cut : ℝ}
    (pack : PrimeJetPacking P n e cut) (hn : 0 < n) (he : 0 < e) (hes : e ≤ s)
    (hcard : Fintype.card B = ∏ p ∈ pack.axes, p) (h : B → ℕ)
    {k : ℕ} (hh : ∀ b, h b ≤ k * pack.jet) :
    ((∑ b, blockCost e (h b) : ℕ) : ℝ) / n ≤ 324 * k * convolutionEnvelope s := by
  have hv : (((∑ i : B × Fin 3, 2 * e * h i.1) : ℕ) : ℝ) ≤ 3 * (2 * (k : ℝ)) * (9 * n) := by
    exact_mod_cast sum_childLength_le_of_packing pack hcard h hh
  have hcost := sum_blockCost_le (fun _ : B => e) h (fun _ => he) (fun _ => hes)
  have hE : 0 ≤ convolutionEnvelope s := zero_le_one.trans (convolutionEnvelope_one_le (he.trans_le hes))
  apply (div_le_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).2
  exact hcost.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ) ≤ 6))
    hE).trans_eq (by ring))

end JetAssembly

end FiniteFourier
end LinearAlgebra
end OAI

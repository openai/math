import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Finite amplification for exact spectral extension

In Theorem 2.4 of *VP and VNP differ over every field*, a uniform multiplicative
discrepancy on a finite list of generators is amplified by doubling or removing
one exponent of a balanced product. Positive integer coefficients make the
resulting variants dominate the balanced product at every competing spectral
point, while their total target value is less than half its scaled target.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

/-- Either double or remove one exponent of the balanced product. -/
def amplificationExponent {ι : Type*} [DecidableEq ι] (e : ℕ) (j : ι × Bool) (i : ι) : ℕ :=
  if i = j.1 then (if j.2 then 2 * e else 0) else e

private noncomputable def variantFactor {ι : Type*} (e : ℕ) (j : ι × Bool) (f : ι → ℝ) : ℝ :=
  if j.2 then f j.1 ^ e else (f j.1 ^ e)⁻¹

private theorem variantFactor_pos {ι : Type*} (e : ℕ) (j : ι × Bool)
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : 0 < variantFactor e j f := by
  dsimp [variantFactor]
  split
  · exact pow_pos (hf _) _
  · exact inv_pos.mpr (pow_pos (hf _) _)

private theorem variantProduct {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ℕ) (j : ι × Bool)
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    (∏ i, f i ^ amplificationExponent e j i) = (∏ i, f i ^ e) * variantFactor e j f := by
  calc
    _ = ∏ i, f i ^ e * (if i = j.1 then variantFactor e j f else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i = j.1
      · subst i
        cases hj : j.2 <;> simp [amplificationExponent, variantFactor, hj, two_mul, pow_add,
          (hf j.1).ne']
      · simp [amplificationExponent, hi]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp

private theorem variantFactor_gap {ι : Type*} (f v : ι → ℝ)
    (hf : ∀ i, 0 < f i)
    (δ : ℝ) (hδ : 0 < δ) (e : ℕ) (B : ℝ) (he : B < (1 + δ) ^ e)
    (i : ι) (hi : 1 + δ ≤ v i / f i ∨ 1 + δ ≤ f i / v i) :
    ∃ j : ι × Bool, B * variantFactor e j f < variantFactor e j v := by
  rcases hi with hi | hi
  · refine ⟨(i, true), ?_⟩
    have h := he.trans_le (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + δ) hi e)
    rw [div_pow] at h
    exact (lt_div_iff₀ (pow_pos (hf i) e)).mp h
  · refine ⟨(i, false), ?_⟩
    have h := he.trans_le (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + δ) hi e)
    rw [div_pow] at h
    change B * (f i ^ e)⁻¹ < (v i ^ e)⁻¹
    rw [← div_eq_mul_inv, div_lt_iff₀ (pow_pos (hf i) e), inv_mul_eq_div]
    exact h

/-- Integer amplification multiplicities with a common scale for finitely many positive weights. -/
theorem amplificationWeights {J : Type*} [Fintype J] (a : J → ℝ) (ha : ∀ j, 0 < a j)
    (t : ℝ) (ht : 0 < t) :
    ∃ L : ℕ, ∃ c : J → ℕ, 0 < L ∧ (∀ j, 0 < c j) ∧
      ∀ j, (L : ℝ) * t < (c j : ℝ) * a j ∧ (c j : ℝ) * a j < (L : ℝ) * (2 * t) := by
  classical
  obtain ⟨L, hL⟩ := exists_nat_gt ((∑ j, a j) / t)
  have hsum : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => (ha j).le
  have hLpos : 0 < (L : ℝ) := (div_nonneg hsum ht.le).trans_lt hL
  have hscale : ∑ j, a j < (L : ℝ) * t := (div_lt_iff₀ ht).mp hL
  refine ⟨L, fun j => ⌊(L : ℝ) * t / a j⌋₊ + 1, by exact_mod_cast hLpos,
    fun j => Nat.succ_pos _, fun j => ?_⟩
  push_cast
  have hj : a j < (L : ℝ) * t :=
    (Finset.single_le_sum (fun k _ => (ha k).le) (Finset.mem_univ j)).trans_lt hscale
  constructor
  · exact (div_lt_iff₀ (ha j)).mp (Nat.lt_floor_add_one _)
  · have hfloor := Nat.floor_le (div_nonneg (mul_nonneg hLpos.le ht.le) (ha j).le)
    have hprod := (le_div_iff₀ (ha j)).mp hfloor
    linarith

/-- A single balanced monomial and positive integer multiples of its variants
separate the target profile from every profile with a uniform multiplicative gap. -/
theorem finiteProfileAmplification {ι H : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (f : ι → ℝ) (v : H → ι → ℝ) (hf : ∀ i, 0 < f i) (hv : ∀ h i, 0 < v h i)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ h, ∃ i, 1 + δ ≤ v h i / f i ∨ 1 + δ ≤ f i / v h i) :
    ∃ e L : ℕ, ∃ c : ι × Bool → ℕ, 0 < e ∧ 0 < L ∧ (∀ j, 0 < c j) ∧
      (∀ h, ∃ j, (L : ℝ) * (∏ i, v h i ^ e) <
        (c j : ℝ) * (∏ i, v h i ^ amplificationExponent e j i)) ∧
      (∑ j, (c j : ℝ) * (∏ i, f i ^ amplificationExponent e j i)) <
        (L : ℝ) * (∏ i, f i ^ e) / 2 := by
  let B : ℝ := 8 * Fintype.card ι
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hs : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBpos : 0 < B := by linarith
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt B (by linarith : 1 < 1 + δ)
  have hep : 0 < e := Nat.pos_of_ne_zero fun h => by
    subst e
    exact (not_lt_of_ge hB) (by simpa using he)
  obtain ⟨L, c, hL, hc, hscale⟩ := amplificationWeights (fun j : ι × Bool => variantFactor e j f)
    (fun j => variantFactor_pos e j f hf) B⁻¹ (inv_pos.mpr hBpos)
  refine ⟨e, L, c, hep, hL, hc, ?_, ?_⟩
  · intro h
    obtain ⟨i, hi⟩ := hgap h
    obtain ⟨j, hj⟩ := variantFactor_gap f (v h) hf δ hδ e B he i hi
    refine ⟨j, ?_⟩
    have hcj : (0 : ℝ) < c j := by exact_mod_cast hc j
    have hfactor : (L : ℝ) < (c j : ℝ) * variantFactor e j (v h) :=
      calc
        (L : ℝ) = ((L : ℝ) * B⁻¹) * B := by simp [hBpos.ne']
        _ < ((c j : ℝ) * variantFactor e j f) * B := mul_lt_mul_of_pos_right (hscale j).1 hBpos
        _ = (c j : ℝ) * (B * variantFactor e j f) := by ring
        _ < _ := mul_lt_mul_of_pos_left hj hcj
    rw [variantProduct e j (v h) (hv h), mul_left_comm (c j : ℝ)]
    simpa only [mul_comm (L : ℝ)] using
      mul_lt_mul_of_pos_left hfactor (Finset.prod_pos fun i _ => pow_pos (hv h i) e)
  · have hsum : (∑ j, (c j : ℝ) * variantFactor e j f) < (L : ℝ) / 2 := calc
      _ < ∑ _j : ι × Bool, (L : ℝ) * (2 * B⁻¹) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => (hscale j).2
      _ = (L : ℝ) / 2 := by
        simp [Fintype.card_prod, B, nsmul_eq_mul]
        field_simp
        norm_num
    calc
      _ = (∑ j, (c j : ℝ) * variantFactor e j f) * (∏ i, f i ^ e) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [variantProduct e j f hf]
        ring
      _ < ((L : ℝ) / 2) * (∏ i, f i ^ e) :=
        mul_lt_mul_of_pos_right hsum (Finset.prod_pos fun i _ => pow_pos (hf i) e)
      _ = _ := by ring

end Spectral

end VPVNP
end Computability
end OAI

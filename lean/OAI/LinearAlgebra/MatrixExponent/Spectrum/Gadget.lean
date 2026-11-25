import OAI.LinearAlgebra.MatrixExponent.Spectrum.Comparison

section
/-! # Uniform exponent savings on the spectrum -/

open scoped NNReal
open Set

namespace OAI.LinearAlgebra.MatrixExponent.Spectrum

private theorem amplify {x y z : ℝ≥0} (h : x < y) (hz : 0 < z) :
    ∃ m : ℕ, x ^ m * z < y ^ m := by
  have hy : 0 < y := zero_le.trans_lt h
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hz) ((div_lt_one hy).mpr h)
  rw [div_pow, div_lt_div_iff₀ (pow_pos hy m) hz, one_mul] at hm
  exact ⟨m, hm⟩

private theorem extend_gain {x y z : ℝ≥0} {m n : ℕ} (h : x < y)
    (hm : x ^ m * z < y ^ m) (hmn : m ≤ n) : x ^ n * z < y ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, pow_add, mul_right_comm]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le h.le k) zero_le).trans_lt
    (mul_lt_mul_of_pos_right hm (pow_pos (zero_le.trans_lt h) k))

/-- The supplier may depend on the point. A finite subcover lets us pay
for any prescribed number of discarded copies with a common exponent. -/
theorem uniform_margin {S I : Type*} [CommSemiring S] [PartialOrder S]
    (hbound : ∀ a : S, ∃ n : ℕ, a ≤ (n : S)) (D : S) (W : I → S) (d : ℕ) (hd : 0 < d)
    (hW : ∀ i, (1 : S) ≤ W i)
    (hgap : ∀ g : S →+* ℝ≥0, Monotone g → ∃ i, g D < g (W i) ^ d) (L : ℕ) :
    ∃ n p : ℕ, 0 < n ∧ p + L < d * n ∧ ∀ g : S →+* ℝ≥0, Monotone g →
      ∃ i, g D ^ n < g (W i) ^ p := by
  classical
  let V (j : I × ℕ) := {v : S → ℝ≥0 | v D < v (W j.1) ^ d ∧
    v D ^ j.2 * v (W j.1) ^ (L + 1) < (v (W j.1) ^ d) ^ j.2}
  have hopen (j : I × ℕ) : IsOpen (V j) := by
    unfold V
    rw [ofPred_and]
    exact (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))
  have hcover : points S ⊆ ⋃ j, V j := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi⟩ := hgap g hg
    have hw : 1 ≤ g (W i) := by simpa only [map_one] using hg (hW i)
    obtain ⟨m, hm⟩ := amplify hi (pow_pos (zero_lt_one.trans_le hw) (L + 1))
    exact mem_iUnion.mpr ⟨(i, m), hi, hm⟩
  obtain ⟨U, hU⟩ := (compact_points hbound).elim_finite_subcover V hopen hcover
  let n := U.sup Prod.snd + L + 1
  have hn : L + 1 ≤ n := by unfold n; omega
  have hdn := hn.trans (Nat.le_mul_of_pos_left n hd)
  refine ⟨n, d * n - (L + 1), by omega, by omega, ?_⟩
  intro g hg
  obtain ⟨⟨i, m⟩, hj, hi, hm⟩ := mem_iUnion₂.mp (hU ⟨g, hg, rfl⟩)
  have hmn : m ≤ U.sup Prod.snd := Finset.le_sup (f := Prod.snd) hj
  have h := extend_gain hi hm (show m ≤ n by unfold n; omega)
  refine ⟨i, lt_of_mul_lt_mul_right (a := g (W i) ^ (L + 1)) ?_ zero_le⟩
  rw [pow_sub_mul_pow _ hdn, pow_mul]
  exact h

end OAI.LinearAlgebra.MatrixExponent.Spectrum
end

section
/-!
# Tensor powers with a finite menu of supply profiles

Round the multiplicity of each supply upwards after dividing by the
power. The product of all supplies dominates two, so a fixed extra
allocation per supply can pay for all selector words.
-/

open scoped NNReal
open Finset

namespace OAI.LinearAlgebra.MatrixExponent.Spectrum

variable {S I : Type*} [CommSemiring S] [PartialOrder S] [Fintype I]

private theorem profile_bound [AddLeftMono S] [MulLeftMono S]
    (hzero : ∀ a : S, 0 ≤ a) (W : I → S) (hW : ∀ i, (1 : S) ≤ W i)
    (hconn : (2 : S) ≤ ∏ i, W i) (p : ℕ) :
    ∃ H : Finset (I → ℕ), (∀ h ∈ H, ∑ i, h i ≤ p + Fintype.card I * (Fintype.card I + 1)) ∧
      ∀ z : ℕ, 0 < z → (∑ i, W i ^ p) ^ z ≤ ∑ h ∈ H, ∏ i, W i ^ (h i * z) := by
  classical
  let k := Fintype.card I
  let B := p + k * (k + 1)
  let H := (Fintype.piFinset (fun _ : I => range (B + 1))).filter
    (fun h => (∀ i, k ≤ h i) ∧ ∑ i, h i ≤ B)
  refine ⟨H, fun _ hh => (mem_filter.mp hh).2.2, fun z hz => ?_⟩
  let A := ∑ h ∈ H, ∏ i, W i ^ ((h i - k) * z)
  have term (f : Fin z → I) : (∏ j, W (f j) ^ p) ≤ A := by
    let count (i : I) := (univ.filter (fun j => f j = i)).card
    have hc : ∑ i, count i = z := by
      simpa only [card_univ, Fintype.card_fin] using
        (card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := f) (by simp)).symm
    let h (i : I) := p * count i / z + (k + 1)
    have hform (i : I) : h i = k + (p * count i / z + 1) :=
      Nat.add_left_comm _ _ _
    have hs : ∑ i, h i ≤ B := by
      have hh : ∑ i, p * count i / z ≤ p := by
        apply Nat.le_of_mul_le_mul_right _ hz
        rw [sum_mul]
        calc
          _ ≤ ∑ i, p * count i := sum_le_sum fun _ _ => Nat.div_mul_le_self _ _
          _ = _ := by rw [← mul_sum, hc]
      simpa only [h, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, ← mul_add]
        using Nat.add_le_add_right hh (k * (k + 1))
    have hh : h ∈ H := by
      have hk (i : I) : k ≤ h i := by rw [hform]; exact Nat.le_add_right _ _
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, hk, hs⟩
      intro i
      exact mem_range.mpr (Nat.lt_succ_of_le ((single_le_sum (fun _ _ => Nat.zero_le _)
        (mem_univ i)).trans hs))
    calc
      _ = ∏ i, W i ^ (p * count i) := by
        rw [← prod_fiberwise' univ f (fun i => W i ^ p)]
        simp only [prod_const, pow_mul, count]
      _ ≤ ∏ i, W i ^ ((h i - k) * z) := by
        apply prod_le_prod
        intro i _
        apply pow_le_pow_right' (hW i)
        rw [hform, Nat.add_sub_cancel_left, mul_comm _ z]
        exact (Nat.lt_mul_div_succ _ hz).le
      _ ≤ A := single_le_sum (f := fun h => ∏ i, W i ^ ((h i - k) * z))
        (fun _ _ => hzero _) hh
  have hk : (k : S) ≤ (∏ i, W i) ^ k := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (Nat.lt_two_pow_self (n := k)).le
    calc
      (k : S) ≤ (k : S) + (t : S) := by simpa using add_le_add_right (hzero (t : S)) (k : S)
      _ = (2 : S) ^ k := by rw [← Nat.cast_add, ← ht, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ _ := pow_le_pow_left' hconn k
  calc
    _ = ∑ f : Fin z → I, ∏ j, W (f j) ^ p := Fintype.sum_pow _ _
    _ ≤ ∑ _f : Fin z → I, A := sum_le_sum fun f _ => term f
    _ = (k : S) ^ z * A := by simp [k, nsmul_eq_mul]
    _ ≤ ((∏ i, W i) ^ k) ^ z * A := mul_le_mul_left (pow_le_pow_left' hk z) A
    _ = _ := by
      unfold A
      rw [← pow_mul, ← prod_pow, mul_sum]
      apply sum_congr rfl
      intro h hh
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      rw [← pow_add, ← Nat.add_mul, Nat.add_sub_of_le ((mem_filter.mp hh).2.1 i)]

/-- A strict spectral advantage yields exact comparisons with a common
budget and a finite list of profiles independent of the tensor power. -/
theorem powered_gadget [Nontrivial S] [Nonempty I]
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : S, 0 ≤ a) (hunit : ∀ a : S, a ≠ 0 → 1 ≤ a)
    (hbound : ∀ a : S, ∃ n : ℕ, a ≤ (n : S)) (D : S) (W : I → S) (d : ℕ) (hd : 0 < d)
    (hW : ∀ i, (1 : S) ≤ W i)
    (hgap : ∀ g : S →+* ℝ≥0, Monotone g → ∃ i, g D < g (W i) ^ d)
    (hconn : (2 : S) ≤ ∏ i, W i) :
    ∃ (b C : ℕ) (H : Finset (I → ℕ)), 0 < b ∧ (∀ h ∈ H, ∑ i, h i < d * b) ∧
      ∀ z : ℕ, 0 < z → D ^ (b * z) ≤ (C : S) * ∑ h ∈ H, ∏ i, W i ^ (h i * z) := by
  let : AddLeftMono S := ⟨fun c a b h => by simpa only [add_comm] using hadd a b c h⟩
  let : MulLeftMono S := ⟨fun c a b h => hmul a b c h⟩
  obtain ⟨b, p, hb, hp, hprice⟩ :=
    uniform_margin hbound D W d hd hW hgap (Fintype.card I * (Fintype.card I + 1))
  have hy : (∑ i, W i ^ p) ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty I›
    have h : (1 : S) ≤ W i ^ p := by simpa using pow_le_pow_left' (hW i) p
    exact ne_of_gt ((lt_of_le_of_ne (hzero 1) zero_ne_one).trans_le
      (h.trans (single_le_sum (f := fun i => W i ^ p) (fun _ _ => hzero _) (mem_univ i))))
  obtain ⟨C, hC⟩ := strictComparison hadd hmul (x := D ^ b) hzero hunit hbound hy (by
    intro g hg
    obtain ⟨i, hi⟩ := hprice g hg
    simp only [map_pow, map_sum]
    exact hi.trans_le (single_le_sum (f := fun i => g (W i) ^ p) (fun _ _ => zero_le) (mem_univ i)))
  obtain ⟨H, hs, he⟩ := profile_bound hzero W hW hconn p
  refine ⟨b, C, H, hb, fun h hh => (hs h hh).trans_lt hp, fun z hz => ?_⟩
  rw [pow_mul]
  exact (hC z).trans (hmul _ _ _ (he z hz))

end OAI.LinearAlgebra.MatrixExponent.Spectrum
end

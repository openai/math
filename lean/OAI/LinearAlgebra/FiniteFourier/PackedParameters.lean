import OAI.LinearAlgebra.FiniteFourier.ConvolutionAtTwoPrimes
import OAI.LinearAlgebra.FiniteFourier.ConvolutionDyadicPacking
import OAI.LinearAlgebra.FiniteFourier.ConvolutionPackingCost

/-! # Simultaneous choice of the three packed prime lists

The progression at two and the disjoint dyadic lists may have different
smoothness exponents. The maximum of their two contraction exponents gives
a common cutoff for the recurrence, independent of the kernel exponent.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Real Filter Finset

/-- The largest supported leaf length of a packed open reduction. -/
def PrimeJetPacking.childCutoff {P : Finset ℕ} {n e : ℕ} {B : ℝ}
    (pack : PrimeJetPacking P n e B) (k : ℕ) : ℕ := k*e*pack.jet

theorem PrimeJetPacking.childCutoff_pos {P : Finset ℕ} {n e k : ℕ} {B : ℝ}
    (pack : PrimeJetPacking P n e B) (hn : 0 < n) (hk : 0 < k) : 0 < pack.childCutoff k := by
  have hvol : 0 < (∏ p ∈ pack.axes, p)*e*pack.jet :=
    (by omega : 0 < 8*n).trans_le pack.volume_lower
  have he : e ≠ 0 := by rintro rfl; simp at hvol
  have hr : pack.jet ≠ 0 := by intro hz; simp [hz] at hvol
  exact Nat.mul_pos (Nat.mul_pos hk (Nat.pos_of_ne_zero he)) (Nat.pos_of_ne_zero hr)

/-- The odd factors of this integer must avoid every protected prime in
the binary prime-axis conversion. -/
def DyadicAxisPacking.orderTimesVolume {F : Type*} [Field F] {η : ℝ} {n B : ℕ}
    (D : DyadicAxisPacking F η n B) : ℕ :=
  axisRootOrder D.pool (8*B) * (∏ p ∈ D.packing.axes, p)

theorem DyadicAxisPacking.orderTimesVolume_pos {F : Type*} [Field F] {η : ℝ} {n B : ℕ}
    (D : DyadicAxisPacking F η n B) : 0 < D.orderTimesVolume := by
  have hpr (p : ℕ) (hp : p ∈ D.pool) : p.Prime :=
    (mem_dyadicEligibleAxes.mp (D.eligible hp)).2.1
  exact Nat.mul_pos (axisRootOrder_pos _ fun p hp => (hpr p hp).two_le)
    (Finset.prod_pos fun p hp => (hpr p (D.packing.axes_subset hp)).pos)

/-- A choice of the three packings with all the width, root and cutoff
conditions used by the simultaneous descent. -/
structure ProtectedPackings (F : Type*) [Field F] (n : ℕ) (σ : ℝ) where
  B₀ : ℕ
  B : ℕ
  width₀ : 6 ≤ B₀
  width : 6 ≤ B
  cutoff₀ : (B₀ : ℝ) ≤ (log n)^2
  cutoff : (B : ℝ) ≤ (log n)^2
  P : Finset ℕ
  M : ℕ
  order_odd : Odd M
  three_dvd : ∀ k : ℕ, 3^k ≤ 8*B₀ → 3^k ∣ M
  atTwo : PrimeJetPacking P n M.totient B₀
  axis_spec : ∀ p ∈ atTwo.axes, p.Prime ∧ p ≤ B₀ ∧ 7 ≤ p ∧ p % 4 = 3 ∧ (p-1)/2 ∣ M
  η : ℝ
  first : DyadicAxisPacking F η n B
  second : DyadicAxisPacking F η n B
  separate : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ first.orderTimesVolume → ¬ l ∣ second.orderTimesVolume
  short : log (max (atTwo.childCutoff 8)
    (max (first.packing.childCutoff 6) (second.packing.childCutoff 6)) : ℕ) ≤ (log n)^σ

/-- For every sufficiently large parent length, the three local circuits
may use one common child cutoff with a fixed contraction exponent. -/
theorem eventually_protectedPackings (F : Type*) [Field F] [CharZero F] :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ᶠ n : ℕ in atTop, Nonempty (ProtectedPackings F n σ) := by
  obtain ⟨η₀, c, hη₀, hη₀', hc, hat⟩ := eventually_atTwoPrimeJetPacking
  obtain ⟨η, hη, hη', hdy⟩ := eventually_dyadicAxisPacking F
  let σ := max (1-η₀/2) (1-η/2)
  have hσ₀ : 1-η₀/2 ≤ σ := le_max_left ..
  have hσ₁ : 1-η/2 ≤ σ := le_max_right ..
  refine ⟨σ, (by linarith : 0 < 1-η₀/2).trans_le hσ₀, max_lt (by linarith) (by linarith), ?_⟩
  have ht : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hwidth₀ := ((tendsto_smoothPackingCutoff hc).comp ht).eventually_ge_atTop 6
  have hwidth := ((tendsto_dyadicPackingCutoff hη).comp ht).eventually_ge_atTop 6
  have hb₀ := ht.eventually (eventually_ceil_power_le_sq (c := 3/c) (by positivity)
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num))
  have hb := ht.eventually (eventually_ceil_power_le_sq (c := 1) (by norm_num)
    (by linarith : (0:ℝ) ≤ 1+η/3) (by linarith))
  filter_upwards [hat, hdy, hwidth₀, hwidth, hb₀, hb, ht.eventually_ge_atTop 1]
    with n ha hd hwidth₀ hwidth hb₀ hb hT
  let T := log (n:ℝ)
  let B₀ := smoothPackingCutoff c T
  let B := dyadicPackingCutoff η T
  let P := atTwoEligiblePrimes B₀ η₀
  let M := atTwoRootOrder P B₀
  change 1 ≤ T at hT
  change (6:ℝ) ≤ B₀ at hwidth₀
  change (6:ℝ) ≤ B at hwidth
  change (⌈3/c * T^(1:ℝ)⌉₊ : ℝ) ≤ T^2 at hb₀
  change (⌈1*T^(1+η/3)⌉₊ : ℝ) ≤ T^2 at hb
  obtain ⟨hodd, hthree, A, hsp, hshort₀⟩ := ha
  obtain ⟨D₁, D₂, hsep⟩ := hd
  change PrimeJetPacking P n M.totient B₀ at A
  change DyadicAxisPacking F η n B at D₁ D₂
  have hcut₀ : (B₀ : ℝ) ≤ T^2 := by simpa only [B₀, smoothPackingCutoff, rpow_one,
    div_mul_eq_mul_div] using hb₀
  have hcut : (B : ℝ) ≤ T^2 := by simpa only [B, dyadicPackingCutoff, one_mul] using hb
  refine ⟨⟨B₀, B, by exact_mod_cast hwidth₀, by exact_mod_cast hwidth, hcut₀, hcut, P, M,
    hodd, hthree, A, ?_, η, D₁, D₂, hsep, ?_⟩⟩
  · intro p hp
    have hmem := A.axes_subset hp
    obtain ⟨hd, _⟩ := Finset.mem_inter.mp hmem
    obtain ⟨hd, _⟩ := Finset.mem_filter.mp hd
    obtain ⟨hpr, _, hup⟩ := mem_dyadicAxisPrimes.mp hd
    exact ⟨hpr, hup, hsp p hp⟩
  · have h₀ : log (A.childCutoff 8 : ℕ) ≤ T^σ := by
      apply le_trans _ (rpow_le_rpow_of_exponent_le hT hσ₀)
      simpa only [PrimeJetPacking.childCutoff, Nat.cast_mul, Nat.cast_ofNat] using hshort₀
    have hD (D : DyadicAxisPacking F η n B) : log (D.packing.childCutoff 6 : ℕ) ≤ T^σ := by
      apply le_trans _ (rpow_le_rpow_of_exponent_le hT hσ₁)
      simpa only [PrimeJetPacking.childCutoff, Nat.cast_mul, Nat.cast_ofNat] using D.short_log
    rcases le_total (A.childCutoff 8) (max (D₁.packing.childCutoff 6) (D₂.packing.childCutoff 6)) with h | h
    · rw [max_eq_right h]
      rcases le_total (D₁.packing.childCutoff 6) (D₂.packing.childCutoff 6) with h' | h'
      · simpa only [max_eq_right h'] using hD D₂
      · simpa only [max_eq_left h'] using hD D₁
    · simpa only [max_eq_left h] using h₀

end FiniteFourier
end LinearAlgebra
end OAI

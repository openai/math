import OAI.LinearAlgebra.FiniteFourier.ConvolutionDyadicSupply
import OAI.LinearAlgebra.FiniteFourier.ConvolutionPrimes
import OAI.LinearAlgebra.FiniteFourier.ConvolutionRootOrders
import OAI.LinearAlgebra.FiniteFourier.ConvolutionDyadicCutoff
import OAI.LinearAlgebra.FiniteFourier.WorkingLengths

/-! # Packing two smooth, separated lists of Fourier axes

At the cutoff `B = ⌈T^(1+η/3)⌉`, even the cardinality bound for each
monochromatic list exceeds `2T`. This supplies the logarithmic mass for
the two applications of the jet packing lemma.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Finset Real

private theorem eventually_dyadicCard_exceeds {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/4) :
    ∀ᶠ T : ℝ in atTop,
      2*T < (⌈T ^ (1+η/3)⌉₊ : ℝ) ^ (1-η/8) := by
  let a := 1 + η / 3
  let b := 1 - η / 8
  have hexp : 0 < a * b - 1 := by
    dsimp [a, b]
    nlinarith [mul_pos hη (show 0 < 5 - η by linarith)]
  filter_upwards [(tendsto_rpow_atTop hexp).eventually_ge_atTop 3,
    eventually_gt_atTop (0:ℝ)] with T h₃ hT
  calc
    _ < T * T ^ (a*b-1) := by nlinarith [mul_le_mul_of_nonneg_left h₃ hT.le]
    _ = T ^ (a*b) := by
      conv_lhs => arg 1; rw [← rpow_one T]
      rw [← rpow_add hT]
      congr 1
      ring
    _ = (T ^ a) ^ b := rpow_mul hT.le _ _
    _ ≤ _ := rpow_le_rpow (rpow_nonneg hT.le _) (Nat.le_ceil _) (by dsimp [b]; linarith)

/-- For one fixed smoothness exponent both separated lists have enough
logarithmic mass at the cutoff used for dyadic transfer. -/
theorem eventually_dyadicLogMass_lists :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ ∀ᶠ T : ℝ in atTop,
      let B := dyadicPackingCutoff η T
      ∃ R ⊆ dyadicEligibleAxes B η, ∃ S ⊆ dyadicEligibleAxes B η,
        2*T < ∑ p ∈ R, log p ∧ 2*T < ∑ q ∈ S, log q ∧
          ∀ p ∈ R, ∀ q ∈ S, ∀ l : ℕ, l.Prime → l ≠ 2 →
            l ∣ p*(p-1) → ¬ l ∣ q*(q-1) := by
  obtain ⟨η, hη, hη', hsupply⟩ := dyadic_good_prime_lists
  refine ⟨η, hη, hη', ?_⟩
  have hcut : Tendsto (dyadicPackingCutoff η) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_dyadicPackingCutoff hη)
  filter_upwards [hcut.eventually (hsupply (η/8) (by positivity)),
    eventually_dyadicCard_exceeds hη hη', hcut.eventually_ge_atTop 6] with T hpair hc hB
  let B := dyadicPackingCutoff η T
  obtain ⟨R, hR, S, hS, hcR, hcS, hd⟩ := hpair
  have hmass (P : Finset ℕ) (hp : P ⊆ dyadicEligibleAxes B η) (hcard : 2*T < P.card) :
      2*T < ∑ p ∈ P, log p := by
    apply hcard.trans_le
    calc
      _ = ∑ _ ∈ P, (1:ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro p h
        have hlow := (mem_dyadicEligibleAxes.mp (hp h)).1.1
        have hh : 3 ≤ p := by change 6 ≤ B at hB; omega
        exact (lt_log_iff_exp_lt (by positivity)).mpr (exp_one_lt_three.trans_le (by exact_mod_cast hh)) |>.le
  exact ⟨R, hR, S, hS, hmass _ hR (hc.trans_le hcR), hmass _ hS (hc.trans_le hcS), hd⟩

/-- The cyclotomic extension degree fixed by a complete list, before packing. -/
noncomputable def listCyclotomicDegree (F : Type*) [Field F] (P : Finset ℕ) (B : ℕ) : ℕ :=
  Module.finrank F (CyclotomicField (axisRootOrder P (8*B)) F)

/-- Packing from one color list at its own cyclotomic degree. -/
structure DyadicAxisPacking (F : Type*) [Field F] (η : ℝ) (n B : ℕ) where
  pool : Finset ℕ
  eligible : pool ⊆ dyadicEligibleAxes B η
  order_dvd : axisRootOrder pool (8*B) ∣ smoothRootOrder B η
  packing : PrimeJetPacking pool n (listCyclotomicDegree F pool B) B
  short_log : log (6 * (listCyclotomicDegree F pool B : ℝ) * packing.jet) ≤ (log n) ^ (1-η/2)

/-- A colored list with sufficient mass can be packed using the degree of
its own root order. -/
private theorem packDyadicList (F : Type*) [Field F] [CharZero F] {n B : ℕ} {η : ℝ}
    (hn : 0 < n) (hB : 6 ≤ B) (hcut : 2 ≤ (B : ℝ) ^ (1-η))
    (hbudget : (smoothRootOrder B η : ℝ) * (B : ℝ)^2 ≤ n)
    (hshort : log (6 * (smoothRootOrder B η : ℝ) * (8*(B : ℝ)^2+1)) ≤ (log n) ^ (1-η/2))
    (P : Finset ℕ) (hP : P ⊆ dyadicEligibleAxes B η) (hmass : 2*log n < ∑ p ∈ P, log p) :
    ∃ D : DyadicAxisPacking F η n B, D.pool = P := by
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hprops (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ B := by
    obtain ⟨⟨hl, hu⟩, hpr, _⟩ := mem_dyadicEligibleAxes.mp (hP hp)
    exact ⟨hpr, by omega, by exact_mod_cast hu⟩
  have hsub := hP.trans (dyadicEligibleAxes_subset_smoothPredecessorPrimes (by omega))
  let M := axisRootOrder P (8*B)
  have hMdvd : M ∣ smoothRootOrder B η := by
    have hf : ⌊8 * (B : ℝ)⌋₊ = 8 * B := by norm_cast; exact Nat.floor_natCast _
    simpa only [M, hf] using axisRootOrder_dvd_smoothRootOrder hB' hcut hsub
  have hM : 0 < M := axisRootOrder_pos _ fun p hp ↦ (hprops p hp).1.two_le
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero (M : F) := ⟨Nat.cast_ne_zero.mpr hM.ne'⟩
  let : FiniteDimensional F (CyclotomicField M F) := IsCyclotomicExtension.finite_of_singleton M F _
  let e := listCyclotomicDegree F P B
  have he : 0 < e := Module.finrank_pos (R := F) (M := CyclotomicField M F)
  have heM : e ≤ M := working_cyclotomic_finrank_le F
  have hes : (e : ℝ) ≤ smoothRootOrder B η :=
    Nat.cast_le.mpr (heM.trans (Nat.le_of_dvd (smoothRootOrder_pos B η) hMdvd))
  have heB := (mul_le_mul_of_nonneg_right hes (sq_nonneg (B : ℝ))).trans hbudget
  obtain ⟨pack⟩ := exists_primeJetPacking P hn he hprops hmass heB
  have hr : (0 : ℝ) < pack.jet := (lt_of_lt_of_le zero_lt_one hB').trans_le pack.jet_lower
  refine ⟨⟨P, hP, hMdvd, pack, ?_⟩, rfl⟩
  change log (6 * (e : ℝ) * pack.jet) ≤ _
  apply le_trans _ hshort
  apply log_le_log (by positivity)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hes (by norm_num)) pack.jet_upper hr.le (by positivity)

/-- At every sufficiently large input length there are two packed boxes.
The head field may in particular be the Gaussian rationals. Each extension
degree is computed from its pool before the subset of axes is selected, and
the two order-times-volume products have disjoint odd-prime support. -/
theorem eventually_dyadicAxisPacking (F : Type*) [Field F] [CharZero F] :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ ∀ᶠ n : ℕ in atTop,
      let B := dyadicPackingCutoff η (log n)
      ∃ D₁ D₂ : DyadicAxisPacking F η n B, ∀ l : ℕ, l.Prime → l ≠ 2 →
        l ∣ axisRootOrder D₁.pool (8*B) * (∏ p ∈ D₁.packing.axes, p) →
          ¬ l ∣ axisRootOrder D₂.pool (8*B) * (∏ q ∈ D₂.packing.axes, q) := by
  obtain ⟨η, hη, hη', hlists⟩ := eventually_dyadicLogMass_lists
  refine ⟨η, hη, hη', ?_⟩
  have hT : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hBt := (tendsto_dyadicPackingCutoff hη).comp hT
  have hcut := ((tendsto_rpow_atTop (show 0 < 1-η by linarith)).comp hBt).eventually_ge_atTop 2
  filter_upwards [hT.eventually hlists, hT.eventually (eventually_dyadicPackingCutoff_bounds hη hη'),
    hcut, hBt.eventually_ge_atTop 6, eventually_gt_atTop (0:ℕ)] with n hmass hbounds hc hB hn
  let B := dyadicPackingCutoff η (log n)
  obtain ⟨R, hR, S, hS, hmR, hmS, hsep⟩ := hmass
  obtain ⟨hshort, hbudget⟩ := hbounds
  rw [exp_log (by positivity)] at hbudget
  change (6 : ℝ) ≤ (B : ℝ) at hB
  have hB' : 6 ≤ B := by exact_mod_cast hB
  obtain ⟨D₁, h₁⟩ := packDyadicList F hn hB' hc hbudget hshort R hR hmR
  obtain ⟨D₂, h₂⟩ := packDyadicList F hn hB' hc hbudget hshort S hS hmS
  subst R S
  refine ⟨D₁, D₂, ?_⟩
  intro l hl hodd
  exact odd_prime_not_dvd_both_packedOrders (8*B) D₁.packing.axes_subset D₂.packing.axes_subset hsep hl hodd

end FiniteFourier
end LinearAlgebra
end OAI

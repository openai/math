import OAI.LinearAlgebra.FiniteFourier.WorkingLengths
import OAI.LinearAlgebra.FiniteFourier.ConvolutionPrimes
import OAI.LinearAlgebra.FiniteFourier.ConvolutionShiftedPrimes

/-! # Packing smooth prime axes with a common root order

The order is the product of the largest prime powers at most `8B` for
primes through the smoothness threshold. Its logarithm is sublinear in
the input logarithm, even after including the jet arithmetic overhead.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Real Finset Filter
open scoped BigOperators Topology

/-- The common order from the proof of Theorem `poly:thm:transfer`. -/
def smoothRootOrder (B η : ℝ) : ℕ :=
  ∏ q ∈ Nat.primesLE ⌊B ^ (1 - η)⌋₊, q ^ Nat.log q ⌊8*B⌋₊

lemma smoothRootOrder_pos (B η : ℝ) : 0 < smoothRootOrder B η :=
  prod_pos fun _ hq ↦ Nat.pow_pos (Nat.mem_primesLE.mp hq).2.pos

/-- Every smooth integer through `8B` divides the common order. -/
lemma dvd_smoothRootOrder {B η : ℝ} {m : ℕ} (hm : 0 < m) (hmB : (m : ℝ) ≤ 8*B)
    (hs : ∀ q ∈ m.primeFactors, (q : ℝ) ≤ B ^ (1-η)) :
    m ∣ smoothRootOrder B η := by
  calc
    m = ∏ q ∈ m.primeFactors, q ^ m.factorization q := Nat.prod_primeFactors_pow_factorization hm.ne'
    _ ∣ ∏ q ∈ m.primeFactors, q ^ Nat.log q ⌊8*B⌋₊ := by
      apply prod_dvd_prod_of_dvd
      intro q hq
      apply pow_dvd_pow
      exact Nat.le_log_of_pow_le (Nat.prime_of_mem_primeFactors hq).one_lt
        ((Nat.ordProj_le q hm.ne').trans (Nat.le_floor hmB))
    _ ∣ smoothRootOrder B η := prod_dvd_prod_of_subset _ _ _ fun q hq ↦
      Nat.mem_primesLE.mpr ⟨Nat.le_floor (hs q hq), Nat.prime_of_mem_primeFactors hq⟩

theorem predecessor_dvd_smoothRootOrder {B η : ℝ} (hB : 0 ≤ B) {p : ℕ}
    (hp : p ∈ smoothPredecessorPrimes B η) : p-1 ∣ smoothRootOrder B η := by
  obtain ⟨_, hp₃, hpB, hs⟩ := (mem_smoothPredecessorPrimes hB).mp hp
  apply dvd_smoothRootOrder (by omega) _ hs
  have : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  linarith

theorem two_pow_dvd_smoothRootOrder {B η : ℝ} (hcut : 2 ≤ B ^ (1-η)) {k : ℕ}
    (hpow : ((2^k : ℕ) : ℝ) ≤ 8*B) : 2^k ∣ smoothRootOrder B η := by
  have hk := Nat.le_log_of_pow_le Nat.one_lt_two (Nat.le_floor hpow)
  apply (pow_dvd_pow 2 hk).trans
  exact dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨Nat.le_floor (by simpa using hcut), Nat.prime_two⟩)

theorem log_smoothRootOrder_le {B η : ℝ} (hB : 1 ≤ B) :
    log (smoothRootOrder B η) ≤ B ^ (1-η) * log (8*B) := by
  let P := Nat.primesLE ⌊B ^ (1-η)⌋₊
  have hcard : (P.card : ℝ) ≤ B ^ (1-η) := by
    have hsub : P ⊆ Icc 1 ⌊B ^ (1-η)⌋₊ := fun q hq ↦
      mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hq).2.one_le, (Nat.mem_primesLE.mp hq).1⟩
    have h : P.card ≤ ⌊B ^ (1-η)⌋₊ := by simpa using card_le_card hsub
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le (by positivity))
  have hf : 1 ≤ ⌊8*B⌋₊ := Nat.le_floor (by push_cast; linarith)
  rw [smoothRootOrder, Nat.cast_prod, log_prod (fun q hq ↦ by
    exact_mod_cast (Nat.pow_pos (Nat.mem_primesLE.mp hq).2.pos).ne')]
  calc
    _ ≤ P.card * log (8*B) := by
      simpa using sum_le_card_nsmul P (fun q ↦ log ((q ^ Nat.log q ⌊8*B⌋₊ : ℕ) : ℝ)) (log (8*B))
        (fun q hq ↦ log_le_log (by exact_mod_cast Nat.pow_pos (Nat.mem_primesLE.mp hq).2.pos)
          ((Nat.cast_le.mpr (Nat.pow_log_le_self q (by omega : ⌊8*B⌋₊ ≠ 0))).trans
            (Nat.floor_le (by linarith))))
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (log_nonneg (by linarith))

/-- The cutoff chosen at input logarithm `T` and prime supply constant `c`. -/
def smoothPackingCutoff (c T : ℝ) : ℕ := ⌈3*T/c⌉₊

theorem tendsto_smoothPackingCutoff {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T ↦ (smoothPackingCutoff c T : ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b*c/3)] with t ht
  exact ((le_div_iff₀ hc).mpr (by linarith)).trans (Nat.le_ceil _)

/-- Finite bound for the product of the common order, the jet length and the
constant factor six in the rational descent. -/
theorem log_smoothRootOrder_jet_le {B η : ℝ} (hB : 1 ≤ B) (hη : η ≤ 1) :
    log (6*(smoothRootOrder B η : ℝ)*(8*B^2+1)) ≤ 3*B^(1-η)*log (8*B) := by
  have hR : 0 < (smoothRootOrder B η : ℝ) := by exact_mod_cast smoothRootOrder_pos B η
  have hexp : 0 ≤ 1-η := by linarith
  have hpoly : log (6*(8*B^2+1)) ≤ 2*log (8*B) := by
    rw [show (2:ℝ)*log (8*B) = log ((8*B)^2) by rw [log_pow]; norm_num]
    apply log_le_log (by positivity)
    nlinarith [sq_nonneg (B-1)]
  rw [show 6*(smoothRootOrder B η : ℝ)*(8*B^2+1) =
    smoothRootOrder B η * (6*(8*B^2+1)) by ring, log_mul hR.ne' (by positivity)]
  have hpow := one_le_rpow hB hexp
  have hnon := log_nonneg (show 1 ≤ 8*B by linarith)
  nlinarith only [log_smoothRootOrder_le (η := η) hB, hpoly,
    mul_nonneg (sub_nonneg.mpr hpow) hnon]

/-- The logarithmic cost of the largest permitted short product, with
extension degree replaced by its upper bound `M`. -/
theorem eventually_log_smoothRootOrder_mul_jet {a η c : ℝ} (ha : 0 < a) (hη : 0 < η) (hη' : η ≤ 1)
    (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, let B : ℝ := smoothPackingCutoff c T
      log (a * (smoothRootOrder B η : ℝ) * (8*B^2+1)) ≤ T ^ (1-η/2) := by
  let A := 3/c+1
  have hA : 0 < A := by dsimp [A]; positivity
  let C := 8 * A^(1-η)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog := (isLittleO_log_rpow_atTop (show 0 < η/2 by positivity)).bound (inv_pos.mpr hC)
  filter_upwards [hlog, eventually_ge_atTop (1:ℝ), eventually_ge_atTop (8*A),
    (tendsto_smoothPackingCutoff hc).eventually (eventually_ge_atTop (1:ℝ)),
    (tendsto_smoothPackingCutoff hc).eventually (eventually_ge_atTop a)]
    with T hl hT hT' hB haB
  let B : ℝ := smoothPackingCutoff c T
  change 1 ≤ B at hB
  change a ≤ B at haB
  change log (a * (smoothRootOrder B η : ℝ) * (8*B^2+1)) ≤ _
  have hTp : 0 < T := by linarith
  have hBp : 0 < B := by linarith
  have hexp : 0 ≤ 1-η := by linarith
  have hlarge : B ≤ A*T := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 3*T/c)
    change (↑⌈3*T/c⌉₊ : ℝ) ≤ (3/c+1)*T
    calc
      _ ≤ 3*T/c+1 := h.le
      _ ≤ 3*T/c+T := by linarith
      _ = _ := by ring
  have hlogB : log (8*B) ≤ 2*log T := by
    rw [← Nat.cast_ofNat (n := 2), ← log_pow]
    apply log_le_log (by positivity)
    nlinarith only [hlarge, mul_nonneg (sub_nonneg.mpr hT') hTp.le]
  have hR : 0 < (smoothRootOrder B η : ℝ) := by exact_mod_cast smoothRootOrder_pos B η
  have hshort : log (a * (smoothRootOrder B η : ℝ) * (8*B^2+1)) ≤
      4*B^(1-η)*log (8*B) := by
    have haB : log (a/6) ≤ log (8*B) := log_le_log (by positivity) (by linarith)
    have hsplit : a*(smoothRootOrder B η : ℝ)*(8*B^2+1) =
        (a/6)*(6*(smoothRootOrder B η : ℝ)*(8*B^2+1)) := by ring
    rw [hsplit, log_mul (by positivity) (by positivity)]
    have hnon := log_nonneg (show 1 ≤ 8*B by linarith)
    nlinarith only [haB, log_smoothRootOrder_jet_le hB hη',
      mul_nonneg (sub_nonneg.mpr (one_le_rpow hB hexp)) hnon]
  have hpow : B^(1-η) ≤ A^(1-η)*T^(1-η) := by
    rw [← mul_rpow hA.le hTp.le]
    exact Real.rpow_le_rpow hBp.le hlarge hexp
  change ‖log T‖ ≤ C⁻¹*‖T^(η/2)‖ at hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hT),
    abs_of_nonneg (Real.rpow_nonneg hTp.le _)] at hl
  calc
    _ ≤ 4*B^(1-η)*log (8*B) := hshort
    _ ≤ 4*(A^(1-η)*T^(1-η))*(2*log T) := by
      gcongr
      exact log_nonneg (by linarith)
    _ = T^(1-η)*(C*log T) := by dsimp [C]; ring
    _ ≤ T^(1-η)*T^(η/2) := by
      apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hTp.le _)
      simpa [mul_assoc, hC.ne'] using mul_le_mul_of_nonneg_left hl hC.le
    _ = _ := by rw [← rpow_add hTp]; congr 1; ring

/-- Short-product length in the rational descent. -/
theorem eventually_log_smoothRootOrder_jet {η c : ℝ} (hη : 0 < η) (hη' : η ≤ 1)
    (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, let B : ℝ := smoothPackingCutoff c T
      log (6 * (smoothRootOrder B η : ℝ) * (8*B^2+1)) ≤ T ^ (1-η/2) :=
  eventually_log_smoothRootOrder_mul_jet (by norm_num) hη hη' hc

/-- Short-product length with the coefficient eight in the integral descent. -/
theorem eventually_log_smoothRootOrder_jet_eight {η c : ℝ} (hη : 0 < η) (hη' : η ≤ 1)
    (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, let B : ℝ := smoothPackingCutoff c T
      log (8 * (smoothRootOrder B η : ℝ) * (8*B^2+1)) ≤ T ^ (1-η/2) :=
  eventually_log_smoothRootOrder_mul_jet (by norm_num) hη hη' hc

/-- The unconditional packing choices in the transfer proof. Every extension
degree bounded by the common order fits the required volume. All selected
predecessors divide the order, and the shorter operand has the stated
logarithmic length. The axis-count estimate is a field of `PrimeJetPacking`. -/
theorem eventually_smoothPrimeJetPacking :
    ∃ η c : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let T := log n
      let B : ℝ := smoothPackingCutoff c T
      let M := smoothRootOrder B η
      (∀ k : ℕ, ((2^k : ℕ) : ℝ) ≤ 8*B → 2^k ∣ M) ∧
      ∀ e : ℕ, 1 ≤ e → e ≤ M →
        ∃ s : PrimeJetPacking (smoothPredecessorPrimes B η) n e B,
          (∀ p ∈ s.axes, p-1 ∣ M) ∧ log (6*(e:ℝ)*s.jet) ≤ T ^ (1-η/2) := by
  obtain ⟨η, c, hη, hη', hc, hsupply⟩ := smoothPredecessor_prime_supply
  have ht : Tendsto (fun n : ℕ ↦ log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := (tendsto_smoothPackingCutoff hc).comp ht
  have htwo := (tendsto_rpow_atTop (show 0 < 1-η by linarith)).comp hb
  refine ⟨η, c, hη, hη', hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ), ht.eventually (eventually_ge_atTop (1:ℝ)),
    hb.eventually (eventually_ge_atTop (1:ℝ)), htwo.eventually (eventually_ge_atTop (2:ℝ)),
    hb.eventually hsupply, ht.eventually (eventually_log_smoothRootOrder_jet hη (by linarith) hc)]
    with n hn hT hB hcut hmass hshort
  let T := log (n : ℝ)
  let B : ℝ := smoothPackingCutoff c T
  let M := smoothRootOrder B η
  change 1 ≤ T at hT
  change 1 ≤ B at hB
  change 2 ≤ B ^ (1-η) at hcut
  change c*B ≤ ∑ p ∈ smoothPredecessorPrimes B η, log p at hmass
  change log (6*(M:ℝ)*(8*B^2+1)) ≤ T^(1-η/2) at hshort
  have hBp : 0 < B := by linarith
  have hMp : (0 : ℝ) < M := by exact_mod_cast smoothRootOrder_pos B η
  refine ⟨fun k hk ↦ two_pow_dvd_smoothRootOrder hcut hk, ?_⟩
  intro e he heM
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have heM' : (e:ℝ) ≤ M := by exact_mod_cast heM
  have hbudget : (e:ℝ)*B^2 ≤ n := by
    apply (log_le_log_iff (by positivity) (by exact_mod_cast hn)).mp
    calc
      _ ≤ log (6*(M:ℝ)*(8*B^2+1)) := by
        apply log_le_log (by positivity)
        calc
          _ ≤ (M:ℝ)*B^2 := mul_le_mul_of_nonneg_right heM' (sq_nonneg _)
          _ ≤ _ := by nlinarith only [mul_nonneg hMp.le (sq_nonneg B), hMp.le]
      _ ≤ T^(1-η/2) := hshort
      _ ≤ T := (rpow_le_rpow_of_exponent_le hT (by linarith : 1-η/2 ≤ 1)).trans_eq (rpow_one T)
  have hsuff : 2*log n < ∑ p ∈ smoothPredecessorPrimes B η, log p := by
    have h := (div_le_iff₀ hc).mp (Nat.le_ceil (3*T/c))
    change 2*T < _
    change 3*T ≤ B*c at h
    linarith
  obtain ⟨s⟩ := exists_primeJetPacking (smoothPredecessorPrimes B η) hn he (fun p hp ↦ by
    obtain ⟨hp, h3, hpB, _⟩ := (mem_smoothPredecessorPrimes hBp.le).mp hp
    exact ⟨hp, h3, hpB⟩) hsuff hbudget
  refine ⟨s, fun p hp ↦ predecessor_dvd_smoothRootOrder hBp.le (s.axes_subset hp), ?_⟩
  apply le_trans _ hshort
  apply log_le_log
  · have hj := s.jet_lower
    have : 0 < (s.jet : ℝ) := hBp.trans_le hj
    positivity
  · gcongr
    exact s.jet_upper

/-- Specialization to the field generated by a primitive `M`th root over the
Gaussian rationals. The same generator supplies every axis and dyadic root. -/
theorem eventually_gaussianCyclotomicPacking :
    ∃ η c : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let T := log n
      let B : ℝ := smoothPackingCutoff c T
      let M := smoothRootOrder B η
      let K := CyclotomicField 4 ℚ
      let E := CyclotomicField M K
      let e := Module.finrank K E
      ∃ (s : PrimeJetPacking (smoothPredecessorPrimes B η) n e B) (ζ : E),
        IsPrimitiveRoot ζ M ∧
        (∀ p ∈ s.axes, IsPrimitiveRoot (ζ ^ (M / (p-1))) (p-1)) ∧
        (∀ k : ℕ, ((2^k : ℕ) : ℝ) ≤ 8*B → IsPrimitiveRoot (ζ ^ (M / 2^k)) (2^k)) ∧
        log (6*(e:ℝ)*s.jet) ≤ T ^ (1-η/2) := by
  obtain ⟨η, c, hη, hη', hc, hpack⟩ := eventually_smoothPrimeJetPacking
  refine ⟨η, c, hη, hη', hc, ?_⟩
  filter_upwards [hpack] with n hn
  let B : ℝ := smoothPackingCutoff c (log n)
  let M := smoothRootOrder B η
  let K := CyclotomicField 4 ℚ
  let E := CyclotomicField M K
  let : NeZero M := ⟨(smoothRootOrder_pos B η).ne'⟩
  let : NeZero (M : K) := ⟨by exact_mod_cast (smoothRootOrder_pos B η).ne'⟩
  obtain ⟨s, hs, hshort⟩ := hn.2 (Module.finrank K E) Module.finrank_pos (working_cyclotomic_finrank_le K)
  exact ⟨s, IsCyclotomicExtension.zeta M K E, IsCyclotomicExtension.zeta_spec M K E,
    fun p hp ↦ working_cyclotomic_root K (hs p hp),
    fun k hk ↦ working_cyclotomic_root K (hn.1 k hk), hshort⟩

end

end

end FiniteFourier
end LinearAlgebra
end OAI

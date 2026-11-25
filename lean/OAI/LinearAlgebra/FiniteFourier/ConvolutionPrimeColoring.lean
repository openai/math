import OAI.LinearAlgebra.FiniteFourier.ConvolutionPrimeFactorCount
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

/-! # Coloring disjoint prime supports

Count red subsets of a finite set of colors. A disjoint ordered pair of supports
can be given its prescribed colors in exactly one out of every two to the power
of the sum of the support sizes colorings. This is the finite averaging step
of the two-lists lemma for dyadic convolution circuits.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset

private theorem prescribedColors_count {ι : Type*} [DecidableEq ι]
    {U S T : Finset ι} (hS : S ⊆ U) (hT : T ⊆ U) (hd : Disjoint S T) :
    (U.powerset.filter (fun C => S ⊆ C ∧ Disjoint C T)).card *
      2 ^ (S.card + T.card) = U.powerset.card := by
  have hs : S ⊆ U \ T := subset_sdiff.mpr ⟨hS, hd⟩
  have heq : U.powerset.filter (fun C => S ⊆ C ∧ Disjoint C T) = Icc S (U \ T) := by
    ext C
    simp only [mem_filter, mem_powerset, mem_Icc, subset_sdiff]
    tauto
  rw [heq, card_Icc_finset hs, card_powerset, ← pow_add]
  congr 1
  have hst := card_le_card hs
  rw [card_sdiff_of_subset hT] at hst ⊢
  have := card_le_card hT
  omega

/-- Given a family of disjoint ordered pairs, one red/blue coloring gives
monochromatic lists whose product of sizes is at least the number of pairs
divided by the largest reciprocal probability of the prescribed colors. -/
theorem exists_disjointSupport_lists {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (P : Finset α) (s : α → Finset ι) (G : Finset (α × α)) (K : ℝ)
    (hpairs : G ⊆ P ×ˢ P)
    (hd : ∀ z ∈ G, Disjoint (s z.1) (s z.2)) (hK : 0 ≤ K)
    (hsize : ∀ z ∈ G, (2 : ℝ) ^ ((s z.1).card + (s z.2).card) ≤ K) :
    ∃ R ⊆ P, ∃ B ⊆ P, (∀ p ∈ R, ∀ q ∈ B, Disjoint (s p) (s q)) ∧
      (G.card : ℝ) ≤ K * R.card * B.card := by
  classical
  let U := P.biUnion s
  let red (C : Finset ι) := P.filter (fun p => s p ⊆ C)
  let blue (C : Finset ι) := P.filter (fun q => Disjoint C (s q))
  let score (C : Finset ι) := (red C).card * (blue C).card
  let fits (C : Finset ι) (z : α × α) := s z.1 ⊆ C ∧ Disjoint C (s z.2)
  obtain ⟨C, _, hmax⟩ := U.powerset.exists_max_image score ⟨∅, by simp⟩
  refine ⟨red C, filter_subset _ _, blue C, filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq
    exact (mem_filter.mp hq).2.mono_left (mem_filter.mp hp).2
  have hcount (z : α × α) (hz : z ∈ G) :
      (U.powerset.card : ℝ) ≤ K * (U.powerset.filter (fun C => fits C z)).card := by
    obtain ⟨hx, hy⟩ := mem_product.mp (hpairs hz)
    have h := prescribedColors_count (U := U) (subset_biUnion_of_mem s hx)
      (subset_biUnion_of_mem s hy) (hd z hz)
    calc
      _ = (2 : ℝ) ^ ((s z.1).card + (s z.2).card) *
          (U.powerset.filter (fun C => fits C z)).card := by
            rw [mul_comm]
            exact_mod_cast h.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hsize z hz) (Nat.cast_nonneg _)
  have hscore (D : Finset ι) : (G.filter (fits D)).card ≤ score D := by
    rw [show score D = ((red D) ×ˢ (blue D)).card by simp [score]]
    apply card_le_card
    intro z hz
    obtain ⟨hz, hfit⟩ := mem_filter.mp hz
    obtain ⟨hp, hq⟩ := mem_product.mp (hpairs hz)
    exact mem_product.mpr ⟨mem_filter.mpr ⟨hp, hfit.1⟩, mem_filter.mpr ⟨hq, hfit.2⟩⟩
  have hsum : (G.card : ℝ) * U.powerset.card ≤ (U.powerset.card : ℝ) * (K * score C) := calc
    _ = ∑ _ ∈ G, (U.powerset.card : ℝ) := by simp
    _ ≤ ∑ z ∈ G, K * (U.powerset.filter (fun D => fits D z)).card := sum_le_sum hcount
    _ = K * ∑ D ∈ U.powerset, ((G.filter (fits D)).card : ℝ) := by
      simp_rw [natCast_card_filter]
      rw [← mul_sum, sum_comm]
    _ ≤ K * ∑ _ ∈ U.powerset, (score C : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact sum_le_sum (fun D hD => by exact_mod_cast (hscore D).trans (hmax D hD))
    _ = _ := by simp; ring
  have hpos : (0 : ℝ) < U.powerset.card := by rw [card_powerset]; positivity
  rw [mul_comm (G.card : ℝ)] at hsum
  have h := le_of_mul_le_mul_left hsum hpos
  simpa [score, mul_assoc] using h

/-- The colors needed by an axis of prime order `p`. -/
def axisOddPrimeSupport (p : ℕ) : Finset ℕ := (p * (p - 1)).primeFactors.erase 2

@[simp] theorem mem_axisOddPrimeSupport {p l : ℕ} (hp : 2 ≤ p) :
    l ∈ axisOddPrimeSupport p ↔ l ≠ 2 ∧ l.Prime ∧ l ∣ p * (p - 1) := by
  have hn : p * (p - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  simp [axisOddPrimeSupport, Nat.mem_primeFactors_of_ne_zero hn]

/-- Eligible primes in the dyadic interval, with smooth predecessor. -/
noncomputable def dyadicEligibleAxes (B : ℕ) (η : ℝ) : Finset ℕ :=
  open Classical in (Ioc (B / 2) B).filter fun p => p.Prime ∧
    ∀ l ∈ (p - 1).primeFactors, (l : ℝ) ≤ (B : ℝ) ^ (1 - η)

@[simp] theorem mem_dyadicEligibleAxes {p B : ℕ} {η : ℝ} :
    p ∈ dyadicEligibleAxes B η ↔
      (B / 2 < p ∧ p ≤ B) ∧ p.Prime ∧
        ∀ l ∈ (p - 1).primeFactors, (l : ℝ) ≤ (B : ℝ) ^ (1 - η) := by
  simp [dyadicEligibleAxes]

/-- Ordered eligible pairs whose axis products have no common odd prime factor. -/
noncomputable def dyadicDisjointPairs (B : ℕ) (η : ℝ) : Finset (ℕ × ℕ) :=
  ((dyadicEligibleAxes B η) ×ˢ (dyadicEligibleAxes B η)).filter
    fun z => Disjoint (axisOddPrimeSupport z.1) (axisOddPrimeSupport z.2)

/-- Given `B^(2-o(1))` eligible disjoint pairs in a dyadic interval, both
disjoint-prime lists have `B^(1-o(1))` members. -/
theorem dyadicPrimeLists_of_pairCount {η : ℝ}
    (hpairs : ∀ δ : ℝ, 0 < δ → ∀ᶠ B : ℕ in Filter.atTop,
      (B : ℝ) ^ (2 - δ) ≤ (dyadicDisjointPairs B η).card)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in Filter.atTop,
      ∃ R ⊆ dyadicEligibleAxes B η, ∃ S ⊆ dyadicEligibleAxes B η,
        (B : ℝ) ^ (1 - ε) ≤ R.card ∧ (B : ℝ) ^ (1 - ε) ≤ S.card ∧
          ∀ p ∈ R, ∀ q ∈ S, ∀ l : ℕ, l.Prime → l ≠ 2 →
            l ∣ p * (p - 1) → ¬ l ∣ q * (q - 1) := by
  classical
  have hδ : 0 < ε / 2 := half_pos hε
  filter_upwards [hpairs (ε / 2) hδ, eventually_two_pow_twice_card_primeFactors_le hδ,
    Filter.eventually_ge_atTop (1 : ℕ)] with B hG hbound hB
  let P := dyadicEligibleAxes B η
  let G := dyadicDisjointPairs B η
  let K := (B : ℝ) ^ (ε / 2)
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hK : 0 < K := Real.rpow_pos_of_pos hB' _
  have hgp : G ⊆ P ×ˢ P := filter_subset _ _
  have hterm {p : ℕ} (hp : p ∈ P) :
      (2 : ℝ) ^ (2 * (axisOddPrimeSupport p).card) ≤ K := by
    have hle := (mem_dyadicEligibleAxes.mp hp).1.2
    have hn : p * (p - 1) ≤ B ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hle (by omega)
    apply le_trans _ (hbound _ hn)
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 2 (card_le_card (erase_subset ..)))
  have hsize (z : ℕ × ℕ) (hz : z ∈ G) :
      (2 : ℝ) ^ ((axisOddPrimeSupport z.1).card + (axisOddPrimeSupport z.2).card) ≤ K := by
    obtain ⟨hp, hq⟩ := mem_product.mp (hgp hz)
    rcases le_total (axisOddPrimeSupport z.1).card (axisOddPrimeSupport z.2).card with h | h
    · exact (pow_le_pow_right₀ (by norm_num) (show _ ≤ 2 * (axisOddPrimeSupport z.2).card by omega)).trans
        (hterm hq)
    · exact (pow_le_pow_right₀ (by norm_num) (show _ ≤ 2 * (axisOddPrimeSupport z.1).card by omega)).trans
        (hterm hp)
  obtain ⟨R, hR, S, hS, hd, hprod⟩ := exists_disjointSupport_lists P axisOddPrimeSupport G K hgp
    (fun _ hz => (mem_filter.mp hz).2) hK.le hsize
  have hPc : P.card ≤ B := by
    have h := card_le_card (show P ⊆ Ioc (B / 2) B from
      fun _ hp => mem_Ioc.mpr (mem_dyadicEligibleAxes.mp hp).1)
    rw [Nat.card_Ioc] at h
    omega
  have hone {r t : ℕ} (ht : t ≤ B) (hfit : (G.card : ℝ) ≤ K * r * t) :
      (B : ℝ) ^ (1 - ε) ≤ r := by
    apply le_of_mul_le_mul_left (a := K * B) _ (mul_pos hK hB')
    calc
      K * B * (B : ℝ) ^ (1 - ε) = (B : ℝ) ^ (2 - ε / 2) := by
        dsimp [K]
        conv_lhs => arg 1; arg 2; rw [← Real.rpow_one (B : ℝ)]
        rw [← Real.rpow_add hB', ← Real.rpow_add hB']
        congr 1
        ring
      _ ≤ (G.card : ℝ) := hG
      _ ≤ K * r * t := hfit
      _ ≤ K * r * B := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ht) (by positivity)
      _ = _ := by ring
  refine ⟨R, hR, S, hS, hone ((card_le_card hS).trans hPc) hprod,
    hone ((card_le_card hR).trans hPc) (by simpa [mul_right_comm] using hprod), ?_⟩
  intro p hp q hq l hl hl₂ hlp hlq
  have hp₂ := (mem_dyadicEligibleAxes.mp (hR hp)).2.1.two_le
  have hq₂ := (mem_dyadicEligibleAxes.mp (hS hq)).2.1.two_le
  exact disjoint_left.mp (hd p hp q hq) ((mem_axisOddPrimeSupport hp₂).mpr ⟨hl₂, hl, hlp⟩)
    ((mem_axisOddPrimeSupport hq₂).mpr ⟨hl₂, hl, hlq⟩)

end FiniteFourier
end LinearAlgebra
end OAI

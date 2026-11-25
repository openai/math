import OAI.LinearAlgebra.FiniteFourier.ConvolutionDescentBound
import OAI.LinearAlgebra.FiniteFourier.ConvolutionPackingCost
import OAI.LinearAlgebra.FiniteFourier.OpenConvolution.OpenDescentLists
import OAI.LinearAlgebra.FiniteFourier.ProtectedCircuit

/-! # Size of the three denominator-protected reductions

The odd prime support of the second root order fixes the protected primes of
the first dyadic list. Clearing that circuit then determines which primes the
second dyadic list must protect. Both lists may choose their wires and child
indices after the protected primes have been specified.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Real Filter

/-- An open reduction over the protected ring with a budget for the total
child length, the longest child, and the work of the two linear maps. -/
def ProtectedPackedList (n : ℕ) (L : Finset ℕ) (volume cutoff : ℕ) (work : ℝ) : Prop :=
  ∃ (B : Type) (_ : Fintype B) (len : B → ℕ)
    (p : OpenConvolution (protectedRationals L) n B len),
    p.RealizesMultiple 1 ∧ (∀ i, 0 < len i ∧ len i ≤ cutoff) ∧ (∑ i, len i) ≤ volume ∧
    (p.linearCost : ℝ) ≤ work

/-- The per-list estimate at a prime packing before taking a common bound on
the cutoff lengths and the logarithmic overhead. -/
noncomputable def PrimeJetPacking.listWork {P : Finset ℕ} {n e : ℕ} {B : ℝ}
    (pack : PrimeJetPacking P n e B) (C β : ℝ) (cutoff : ℕ) : ℝ :=
  C * n * (1 + log B)^2 * (((pack.axes.card : ℝ) + 1)^β +
    (1 + log (2 + pack.jet)) * convolutionEnvelope cutoff)

theorem convolutionEnvelope_mono_of_pos {s t : ℕ} (hs : 0 < s) (hst : s ≤ t) :
    convolutionEnvelope s ≤ convolutionEnvelope t := by
  obtain ⟨j, hj, he⟩ := exists_convolutionEnvelope_eq hs
  rw [he]
  simp only [convolutionEnvelope, dite_eq_left (hs.trans_le hst), add_le_add_iff_left]
  exact Finset.le_sup' convolutionRate
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans hst⟩)

theorem PrimeJetPacking.listWork_le {P : Finset ℕ} {n e s t : ℕ} {B C β : ℝ}
    (pack : PrimeJetPacking P n e B) (hC : 0 ≤ C) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hB : 1 ≤ B) (hcut : B ≤ (log n)^2) (hT : 3 ≤ log n)
    (hs : 0 < s) (hst : s ≤ t) :
    pack.listWork C β s ≤ 135*C*n *
      (convolutionGauge β (log n) + (log (log n))^3 * convolutionEnvelope t) := by
  have he := convolutionEnvelope_mono_of_pos hs hst
  have hL : 0 ≤ (log (log n))^3 := by
    have := log_nonneg (show 1 ≤ log n by linarith)
    positivity
  have h := pack.normalizedCost_le hβ hβ' (zero_le_one.trans (convolutionEnvelope_one_le hs))
    hB hcut hT
  calc
    _ = C*n*((1 + log B)^2*(((pack.axes.card : ℝ) + 1)^β +
        (1 + log (2 + pack.jet)) * convolutionEnvelope s)) := by unfold listWork; ring
    _ ≤ C*n*(135*(convolutionGauge β (log n) + (log (log n))^3 * convolutionEnvelope s)) :=
      mul_le_mul_of_nonneg_left h (mul_nonneg hC (Nat.cast_nonneg _))
    _ = 135*C*n*(convolutionGauge β (log n) + (log (log n))^3 * convolutionEnvelope s) := by ring
    _ ≤ _ := by gcongr

/-- Combine an odd-denominator list with two families over protected rings.
The order-times-volume products determine the protected sets. The child
types and their lengths may depend on the actual circuit in the first family. -/
theorem assembleProtectedPackedLists {n a b s₀ s₁ s₂ : ℕ} {w₀ w₁ w₂ : ℝ}
    (hb : 0 < b)
    (hdisj : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ a → ¬ l ∣ b)
    (h₀ : ProtectedPackedList n {2} (3*8*(9*n)) s₀ w₀)
    (h₁ : ∀ L : Finset ℕ, (∀ l ∈ L, l.Prime ∧ l ≠ 2 ∧ ¬ l ∣ a) →
      ProtectedPackedList n L (3*6*(9*n)) s₁ w₁)
    (h₂ : ∀ L : Finset ℕ, (∀ l ∈ L, l.Prime ∧ l ≠ 2 ∧ ¬ l ∣ b) →
      ProtectedPackedList n L (3*6*(9*n)) s₂ w₂) :
    ∃ (B : Type) (_ : Fintype B) (len : B → ℕ) (p : OpenConvolution ℤ n B len),
      p.RealizesMultiple 1 ∧ (∀ i, 0 < len i ∧ len i ≤ max s₀ (max s₁ s₂)) ∧
      (∑ i, len i) ≤ 540*n ∧ (p.linearCost : ℝ) ≤ w₀ + w₁ + w₂ + 4*n := by
  let L := b.primeFactors.erase 2
  have hL : ∀ l ∈ L, l.Prime ∧ l ≠ 2 ∧ ¬ l ∣ a := by
    intro l hl
    obtain ⟨hodd, hf⟩ := Finset.mem_erase.mp hl
    obtain ⟨hpr, hd, _⟩ := Nat.mem_primeFactors.mp hf
    exact ⟨hpr, hodd, fun ha => hdisj l hpr hodd ha hd⟩
  obtain ⟨B₀, f₀, len₀, p₀, hp₀, hr₀, hv₀, hw₀⟩ := h₀
  obtain ⟨B₁, f₁, len₁, p₁, hp₁, hr₁, hv₁, hw₁⟩ := h₁ L hL
  let _ := f₀
  let _ := f₁
  obtain ⟨q₀, D₀, _, hd₀, hi₀, ho₀, hq₀⟩ := p₀.clearProtected hp₀
  obtain ⟨q₁, D₁, hpos, hd₁, hi₁, ho₁, hq₁⟩ := p₁.clearProtected hp₁
  let U := D₁.primeFactors.erase 2
  have hU : ∀ l ∈ U, l.Prime ∧ l ≠ 2 ∧ ¬ l ∣ b := by
    intro l hl
    obtain ⟨hodd, hf⟩ := Finset.mem_erase.mp hl
    have hpr := (Nat.mem_primeFactors.mp hf).1
    refine ⟨hpr, hodd, fun hd => ?_⟩
    exact Finset.disjoint_left.mp (disjoint_oddFactors_of_mem_denominatorsAvoiding hd₁)
      hl (Finset.mem_erase.mpr ⟨hodd, hpr.mem_primeFactors hd hb.ne'⟩)
  obtain ⟨B₂, f₂, len₂, p₂, hp₂, hr₂, hv₂, hw₂⟩ := h₂ U hU
  let _ := f₂
  obtain ⟨q₂, D₂, _, hd₂, hi₂, ho₂, hq₂⟩ := p₂.clearProtected hp₂
  obtain ⟨k, hk⟩ := gcd_eq_pow_two_of_avoids_oddFactors hpos hd₂
  obtain ⟨p, hp, hw⟩ := OpenConvolution.threeListBezout q₀ q₁ q₂ hq₀ hq₁ hq₂
    (odd_of_mem_denominatorsAvoiding_two hd₀) hk
  refine ⟨_, inferInstance, _, p, hp, ?_, OpenConvolution.childLengthSum_le hv₀ hv₁ hv₂, ?_⟩
  · rintro (i | (i | i))
    · exact ⟨(hr₀ i).1, (hr₀ i).2.trans (le_max_left ..)⟩
    · exact ⟨(hr₁ i).1, (hr₁ i).2.trans ((le_max_left ..).trans (le_max_right ..))⟩
    · exact ⟨(hr₂ i).1, (hr₂ i).2.trans ((le_max_right ..).trans (le_max_right ..))⟩
  · have hsize : p.linearCost ≤ p₀.linearCost+p₁.linearCost+p₂.linearCost+4*n := by
      simp only [OpenConvolution.linearCost, hi₀, ho₀, hi₁, ho₁, hi₂, ho₂] at hw ⊢
      omega
    have hsize' : (p.linearCost : ℝ) ≤ p₀.linearCost+p₁.linearCost+p₂.linearCost+4*n := by
      exact_mod_cast hsize
    linarith only [hsize', hw₀, hw₁, hw₂]

end FiniteFourier
end LinearAlgebra
end OAI

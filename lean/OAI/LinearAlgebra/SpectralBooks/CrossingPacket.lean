import OAI.LinearAlgebra.SpectralBooks.GroundFieldComparison
import OAI.LinearAlgebra.SpectralBooks.CutSpectrum

/-!
# Straightening one packet of crossing wires

When every normalized point assigns the crossing a value at most the larger
of the two noncrossing pairings, a direct sum gives a strict comparison even
at points where the crossing saturates the four-point inequality. Expansion
of a power trades the crossing packet for two side pairings whose widths
add to the original packet width.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators NNReal Classical
noncomputable section

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- The source classes `X,A,B` may be any three nonzero tensors. For the
four marked sites they are respectively the crossing and the two side
pairings, each initially of width one. -/
theorem exists_relative_packet (X A B : TensorClass.{v} I K) (hX : X ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (four : ∀ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop),
      f.val X ≤ max (f.val A) (f.val B)) {σ : ℝ} (hσ : 0 < σ) :
    ∃ b : ℕ, 0 < b ∧ ∀ R : Raw.{v} I K, ofRaw R = X^b →
      ∃ L : ℕ, (L:ℝ) ≤ (2:ℝ)^(σ*b) ∧ ∃ z : Fin L → (∀ i, R.Leg i) → K,
        R.coeff = ∑ l, z l ∧ ∀ l, ∃ u v : ℕ, u + v = b ∧ ofRaw {R with coeff := z l} ≤ A^u * B^v := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / σ)
  have hk' : 2 < σ*k := by simpa [mul_comm] using (div_lt_iff₀ hσ).mp hk
  have hkpos : 0 < k := by
    exact_mod_cast (div_pos (by norm_num : (0:ℝ) < 2) hσ).trans hk
  have nz : A^k + B^k ≠ 0 := by
    intro h
    apply pow_ne_zero k hA
    apply le_antisymm _ (zero_le_tensor _)
    calc
      A^k ≤ A^k + B^k := by simpa using add_mono (le_refl (A^k)) (zero_le_tensor (B^k))
      _ = 0 := h
  have gap (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
      f.val (X ^ k) < f.val (A^k + B^k) := by
    let φ := normalizedSpectrum.toRingHom f
    change φ (X^k) < φ (A^k + B^k)
    rw [map_add, map_pow, map_pow, map_pow]
    have apos : 0 < φ A := spectral_value_pos f hA
    have bpos : 0 < φ B := spectral_value_pos f hB
    rcases le_max_iff.mp (four f) with h | h
    · exact (pow_le_pow_left' h k).trans_lt (lt_add_of_pos_right _ (pow_pos bpos k))
    · exact (pow_le_pow_left' h k).trans_lt (lt_add_of_pos_left _ (pow_pos apos k))
  obtain ⟨C, hC, hp⟩ := strictSpectralComparison I K (X^k) (A^k+B^k) (pow_ne_zero k hX) nz gap
  let P := Fin C × (Fin C → Bool)
  let e := Fintype.equivFin P
  let factors (w : Fin C → Bool) (t : Fin C) := if w t then A^k else B^k
  let S (p : P) := ∏ t, factors p.2 t
  have hs : C • ((A^k + B^k)^C) = ∑ p, S p := by
    change _ = ∑ p : Fin C × (Fin C → Bool), ∏ t, if p.2 t then A^k else B^k
    rw [Fintype.sum_prod_type]
    simp_rw [← Fintype.prod_sum (fun (_ : Fin C) (b : Bool) => if b then A^k else B^k)]
    simp
  refine ⟨k*C, Nat.mul_pos hkpos hC, fun R hR => ?_⟩
  obtain ⟨z, hz, hu⟩ := images_of_le_sum R S (by rw [hR, ← hs, pow_mul]; exact hp C hC)
  have hcost : (Fintype.card P:ℝ) ≤ (2:ℝ)^(σ*((k*C:ℕ):ℝ)) := by
    have hpow : (C:ℝ) ≤ (2:ℝ)^C := by exact_mod_cast (Nat.lt_two_pow_self (n:=C)).le
    calc
      _ = C * (2:ℝ)^C := by simp [P]
      _ ≤ (2:ℝ)^C * (2:ℝ)^C := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (2:ℝ)^(2*(C:ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2), two_mul]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [Nat.cast_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hk'.le (Nat.cast_nonneg _)
  refine ⟨Fintype.card P,hcost,z ∘ e.symm, hz.trans (Fintype.sum_equiv e _ _ fun p => by simp), ?_⟩
  intro l
  let w := (e.symm l).2
  let left := (Finset.univ : Finset (Fin C)).filter (fun i => w i = true)
  let right := (Finset.univ : Finset (Fin C)).filter (fun i => ¬w i = true)
  have hc : left.card + right.card = C := by
    simpa [left, right] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin C)))
      (fun i => w i = true)
  refine ⟨k * left.card, k * right.card, by rw [← Nat.mul_add, hc], (hu (e.symm l)).trans_eq ?_⟩
  change (∏ t, if w t then A^k else B^k) = _
  rw [Finset.prod_ite]
  simp [left, right, pow_mul]

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI

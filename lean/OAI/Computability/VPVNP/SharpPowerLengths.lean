import OAI.Computability.VPVNP.TensorPowerLengths
import Mathlib.Data.Nat.Find

/-! # Selecting a tensor power with polynomial overhead in its length

For a projection requiring `A (h+1)^D B^h` input bits, choose the largest power
which fits at an available small-circuit length. The next power's requirement is
an upper bound on that length. Its polynomial factor stays separate from `B^h`.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- At a length admitting the requested starting index, select a maximal fitting
index and compare with its successor. -/
private theorem exists_last_fitting_index (length : ℕ → ℕ) (growth : ∀ h, h < length h)
    {H n : ℕ} (fits : length H ≤ n) :
    ∃ h ≥ H, length h ≤ n ∧ n < length (h + 1) := by
  let h := Nat.findGreatest (fun t => length t ≤ n) n
  have hH : H ≤ n := (growth H).le.trans fits
  have hin : length h ≤ n := Nat.findGreatest_spec (P := fun t => length t ≤ n) hH fits
  have hnext : h + 1 ≤ n := (growth h).trans_le hin
  exact ⟨h, Nat.le_findGreatest hH fits, hin,
    lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun t => length t ≤ n) (Nat.lt_succ_self h) hnext)⟩

/-- Unboundedly many small circuits for `P` give arbitrarily high powers with the
same exponential rate in their circuit-size bound. -/
theorem arbitrarily_large_powers_of_sharp_projections {F : Type*} [CommRing F]
    {V : ℕ → Type*} (forms : (h : ℕ) → MvPolynomial (V h) F)
    {A B C D : ℕ} (hA : 0 < A) (hB : 1 < B)
    (projections : ∀ h n, A * (h + 1)^D * B^h ≤ n →
      ∃ φ : Projection F (Fin n × Bool) (V h),
        φ.hom (MvPolynomial.map (Int.castRingHom F) (P n)) = forms h)
    (small : ∀ N, ∃ n ≥ N, circuitSize (MvPolynomial.map (Int.castRingHom F) (P n)) ≤ n^C) :
    ∀ H, ∃ h ≥ H, circuitSize (forms h) ≤ (A * B)^C * (h + 2)^(D*C) * (B^h)^C := by
  let length (h : ℕ) := A * (h + 1)^D * B^h
  have growth (h : ℕ) : h < length h := by
    apply (Nat.lt_pow_self hB : h < B^h).trans_le
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hA (Nat.pow_pos (Nat.succ_pos _)))
  intro H
  obtain ⟨n, hn, hs⟩ := small (length H)
  obtain ⟨h, hH, hlow, hhigh⟩ := exists_last_fitting_index length growth hn
  obtain ⟨φ, hφ⟩ := projections h n hlow
  refine ⟨h, hH, ?_⟩
  calc
    circuitSize (forms h) ≤ circuitSize (MvPolynomial.map (Int.castRingHom F) (P n)) :=
      hφ ▸ circuitSize_projection_le φ _
    _ ≤ n^C := hs
    _ ≤ (length (h + 1))^C := Nat.pow_le_pow_left hhigh.le C
    _ = _ := by
      change (A * (h + 2)^D * B^(h + 1))^C = _
      rw [pow_succ B h]
      simp only [mul_pow, pow_mul]
      ring

end VPVNP
end Computability
end OAI

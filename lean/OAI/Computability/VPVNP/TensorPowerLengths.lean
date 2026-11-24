import OAI.Computability.VPVNP.PaddedQuery
import Mathlib.Data.Nat.Log

/-! # Selecting powers at lengths with a small circuit

A polynomial-size literal encoding of each tensor power suffices for cube
exclusion if its polynomial exponent is absolute. Use the largest power whose
encoding fits at the given length. The cutoff is selected after the circuit
length, which can belong to an arbitrary unbounded set.
-/

namespace OAI
namespace Computability
namespace VPVNP

theorem arbitrarily_large_powers_of_small_circuits {F : Type*} [CommRing F]
    {V : ℕ → Type*} (forms : (h : ℕ) → MvPolynomial (V h) F)
    {A B C : ℕ} (hA : 0 < A) (hB : 1 < B)
    (projections : ∀ h n, A * B^h ≤ n → ∃ φ : Projection F (Fin n × Bool) (V h),
      φ.hom (MvPolynomial.map (Int.castRingHom F) (P n)) = forms h)
    (small : ∀ N, ∃ n ≥ N, circuitSize (MvPolynomial.map (Int.castRingHom F) (P n)) ≤ n^C) :
    ∀ H, ∃ h ≥ H, circuitSize (forms h) ≤ (A * B)^C * (B^h)^C := by
  intro H
  obtain ⟨n, hn, hs⟩ := small (A * B^H)
  let h := Nat.log B (n/A)
  have hquot : B^H ≤ n/A := (Nat.le_div_iff_mul_le hA).mpr (by simpa [mul_comm] using hn)
  have hpos : n/A ≠ 0 := Nat.ne_of_gt ((Nat.pow_pos (by omega : 0 < B)).trans_le hquot)
  have hlow : A * B^h ≤ n := by
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hA).mp (Nat.pow_log_le_self B hpos)
  have hhigh : n ≤ A * B * B^h := by
    have bound := (Nat.div_lt_iff_lt_mul hA).mp (Nat.lt_pow_succ_log_self hB (n/A))
    simpa [h, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using bound.le
  obtain ⟨φ, hφ⟩ := projections h n hlow
  refine ⟨h, Nat.le_log_of_pow_le hB hquot, ?_⟩
  calc
    circuitSize (forms h) ≤ circuitSize (MvPolynomial.map (Int.castRingHom F) (P n)) :=
      hφ ▸ circuitSize_projection_le φ _
    _ ≤ n^C := hs
    _ ≤ (A * B * B^h)^C := Nat.pow_le_pow_left hhigh C
    _ = _ := mul_pow _ _ _

end VPVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.PackedDeckCandidateScore

/-! # A logarithmic working width for the varying-norm score -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckCandidate

open PackedDeckScore

variable {B G : Type*} [Fintype G] {m w : ℕ}

/-- Working width sufficient for input counts, cleared mean numerators, and every scalar
charge before summation over relative bins. -/
def choiceBits (N D K L : ℕ) :=
  Nat.log2 (K + L + 3*D*N^2*K^2 + 2*N^2*L*K) + 1

private theorem sum_bound (f : G → ℕ) (K : ℕ) (hk : ∀ g, f g ≤ K) : (∑ g, f g) ≤ Fintype.card G*K := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hk g)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] using h

/-- The capacity needed in the score circuit follows from the magnitude of the raw counts and
the common-denominator numerators. -/
theorem charge_fits (D K L : ℕ) (x : Input B G m w → Bool)
    (counts_le : ∀ p t g, inputCounts x p t g ≤ K) (mean_le : ∀ t, meanNumerator x t ≤ L)
    (width : choiceBits (Fintype.card G) D K L ≤ w) (i : Fin m) (neg : Bool) (t : B) :
    charge D x i neg t < 2^w := by
  let n := Fintype.card G
  have h (p) := sum_bound (inputCounts x p t) K (counts_le p t)
  have hs := sum_bound (fun g => inputCounts x (some i) t g * inputCounts x (some i) t g)
    (K*K) (fun g => Nat.mul_le_mul (counts_le _ _ g) (counts_le _ _ g))
  have hc : charge D x i neg t ≤ K + L + 3*D*n^2*K^2 + 2*n^2*L*K := by
    cases neg with
    | false =>
      change D*n*(∑ g, inputCounts x (some i) t g * inputCounts x (some i) t g) +
        2*D*(∑ g, inputCounts x none t g)*(∑ g, inputCounts x (some i) t g) ≤ _
      calc
        _ ≤ D*n*(n*(K*K)) + 2*D*(n*K)*(n*K) := Nat.add_le_add (Nat.mul_le_mul_left _ hs)
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ (h none)) (h (some i)))
        _ = 3*D*n^2*K^2 := by ring
        _ ≤ _ := by omega
    | true =>
      change 2*n*(meanNumerator x t)*(∑ g, inputCounts x (some i) t g) ≤ _
      calc
        _ ≤ 2*n*L*(n*K) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (mean_le t)) (h _)
        _ = 2*n^2*L*K := by ring
        _ ≤ _ := by omega
  exact (lt_of_le_of_lt hc Nat.lt_log2_self).trans_le (Nat.pow_le_pow_right (by decide) width)

/-- Input fields are representable at the same working width. -/
theorem fields_fit (N D K L : ℕ) :
    K < 2^choiceBits N D K L ∧ L < 2^choiceBits N D K L := by
  have h : K + L + 3*D*N^2*K^2 + 2*N^2*L*K < 2^choiceBits N D K L := Nat.lt_log2_self
  omega

end PackedDeckCandidate

end BorderVNP
end Computability
end OAI

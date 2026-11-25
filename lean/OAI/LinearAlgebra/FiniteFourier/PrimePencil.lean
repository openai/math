import OAI.LinearAlgebra.FiniteFourier.PrimePencilCoefficients
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-! # Potter's identity for the matrix pencil

Normal ordering at a central scalar `q` gives the Gaussian binomial expansion.
At a primitive root of order `b` its mixed terms vanish. The result applies to
matrices and to other associative algebras over the coefficient domain.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

section Expansion

variable {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A] {q : K} {U V : A}

private theorem commuted_power (hVU : V * U = q • (U * V)) (k : ℕ) :
    V ^ k * U = q ^ k • (U * V ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ V, mul_assoc, hVU, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc,
      smul_smul, ← mul_assoc, pow_succ q, mul_comm q, mul_assoc]

private theorem collect_adjacent {M : Type*} [AddCommMonoid M] (n : ℕ) (a b c : ℕ → M)
    (h₀ : c 0 = a 0) (hs : ∀ k < n, c (k + 1) = a (k + 1) + b k)
    (hn : c (n + 1) = b n) :
    ∑ k ∈ Finset.range (n + 1), (a k + b k) = ∑ k ∈ Finset.range (n + 2), c k := by
  rw [Finset.sum_add_distrib, Finset.sum_range_succ' a, Finset.sum_range_succ b,
    Finset.sum_range_succ c, Finset.sum_range_succ' c, h₀, hn,
    Finset.sum_congr rfl (fun k hk => hs k (Finset.mem_range.mp hk)), Finset.sum_add_distrib]
  abel

/-- Normal ordering when the reversed product picks up a scalar factor. -/
theorem quantumBinom_pow_add (hVU : V * U = q • (U * V)) (n : ℕ) :
    (U + V) ^ n = ∑ k ∈ Finset.range (n + 1),
      quantumBinom q n k • (U ^ (n - k) * V ^ k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let a k := (q ^ k * quantumBinom q n k) • (U ^ (n + 1 - k) * V ^ k)
    let b k := quantumBinom q n k • (U ^ (n - k) * V ^ (k + 1))
    let c k := quantumBinom q (n + 1) k • (U ^ (n + 1 - k) * V ^ k)
    rw [pow_succ, ih, Finset.sum_mul]
    calc
      _ = ∑ k ∈ Finset.range (n + 1), (a k + b k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : n + 1 - k = n - k + 1 := by
          have := Finset.mem_range.mp hk
          omega
        dsimp [a, b]
        rw [mul_add, smul_mul_assoc, smul_mul_assoc, mul_assoc, commuted_power hVU,
          mul_smul_comm, smul_smul, ← mul_assoc, hk', pow_succ U, pow_succ V,
          mul_comm (quantumBinom q n k), mul_assoc (U ^ (n - k)) (V ^ k) V]
      _ = ∑ k ∈ Finset.range (n + 2), c k := by
        apply collect_adjacent
        · simp [a, c, quantumBinom_zero_right]
        · intro k _
          simp only [a, b, c, quantumBinom_succ_succ, Nat.add_sub_add_right, add_smul]
        · simp [b, c, quantumBinom_self]

end Expansion

variable {K A : Type*} [CommRing K] [Semiring A] [Algebra K A]
  {q : K} {b : ℕ}

/-- When the interior Gaussian coefficients vanish, only the two pure powers survive. -/
theorem potter_pow_add_of_vanishing (hb : 0 < b)
    (hmix : ∀ k, 0 < k → k < b → quantumBinom q b k = 0) {U V : A}
    (hVU : V * U = q • (U * V)) : (U + V) ^ b = U ^ b + V ^ b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  rw [quantumBinom_pow_add hVU, Finset.sum_range_succ, Finset.sum_range_succ']
  have hmixed : ∑ k ∈ Finset.range m,
      quantumBinom q (m + 1) (k + 1) • (U ^ ((m + 1) - (k + 1)) * V ^ (k + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have := Finset.mem_range.mp hk
    rw [hmix (k + 1) (by omega) (by omega), zero_smul]
  simp only [Nat.add_sub_add_right] at hmixed
  simp [hmixed]

/-- Potter's identity at a primitive root over an integral domain. -/
theorem potter_pow_add [IsDomain K] (hb : 0 < b) (hq : IsPrimitiveRoot q b) {U V : A}
    (hVU : V * U = q • (U * V)) : (U + V) ^ b = U ^ b + V ^ b :=
  potter_pow_add_of_vanishing hb (fun _ => quantumBinom_eq_zero_of_primitiveRoot hq) hVU

/-- In an ordered family where later terms quantum-commute past all earlier ones,
the power of the pencil equals the sum of the powers of the summands. -/
theorem potter_fin_sum_of_vanishing (hb : 0 < b)
    (hmix : ∀ k, 0 < k → k < b → quantumBinom q b k = 0) {h : ℕ} (T : Fin h → A)
    (hcomm : ∀ i j, i < j → T j * T i = q • (T i * T j)) :
    (∑ i, T i) ^ b = ∑ i, T i ^ b := by
  induction h with
  | zero => simp [zero_pow hb.ne']
  | succ n ih =>
    have hVU : T (Fin.last n) * (∑ i : Fin n, T i.castSucc) =
        q • ((∑ i : Fin n, T i.castSucc) * T (Fin.last n)) := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => hcomm _ _ i.castSucc_lt_last
    rw [Fin.sum_univ_castSucc T, potter_pow_add_of_vanishing hb hmix hVU, Fin.sum_univ_castSucc (fun i => T i ^ b)]
    rw [ih (fun i => T i.castSucc) (fun i j hij => hcomm _ _ hij)]

/-- The ordered-family identity at a primitive root over a domain. -/
theorem potter_fin_sum [IsDomain K] (hb : 0 < b) (hq : IsPrimitiveRoot q b) {h : ℕ}
    (T : Fin h → A) (hcomm : ∀ i j, i < j → T j * T i = q • (T i * T j)) :
    (∑ i, T i) ^ b = ∑ i, T i ^ b :=
  potter_fin_sum_of_vanishing hb (fun _ => quantumBinom_eq_zero_of_primitiveRoot hq) T hcomm

end FiniteFourier
end LinearAlgebra
end OAI

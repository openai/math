import OAI.Computability.VPVNP.UniversalMachine

/-!
# Clock and length bounds for compiled payload queries

Each query can scan the full input and then move at most the length of the
payload to reach the addressed bit. The literal table contributes enough
prefix bits for a cubic bound on the total number of steps.
-/

namespace OAI
namespace Computability
namespace VPVNP

open UniversalMachine

/-- The unary state-count header alone has one bit for each running state. -/
theorem queryPrefix_lower {p : Program} {t : ℕ} (ht : t + 1 ≤ p.extra) :
    t + 2 ≤ (programPrefix p).length := by
  have hpos : p.extra ≠ 0 := by omega
  have htable : p.extra ≤ (tableBits p).length := by
    simp [tableBits, hpos, unary]
    omega
  simp [programPrefix, unary]
  omega

/-- The fixed clock of §1.1 allows a full scan and a payload traversal for
each query, plus the halting instruction. -/
theorem querySteps_le_clock {t k ℓ n : ℕ} (hn : n = ℓ + k) (ht : t + 2 ≤ ℓ) :
    t * (n + k + 1) + 1 ≤ n ^ clockExponent := by
  have hn2 : 2 ≤ n := by omega
  calc
    t * (n + k + 1) + 1 ≤ (t + 1) * (n + k + 1) := by rw [Nat.succ_mul]; omega
    _ ≤ n * (2 * n) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ n * (n * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hn2)
    _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]
    _ ≤ n ^ clockExponent := Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ clockExponent)

/-- A quadratic table encoding preserves polynomial bounds on the number of
queries, the number of query-program states, and the payload length. -/
theorem queryInputLength_le {t q k ℓ A B : ℕ}
    (hprefix : ℓ ≤ A * ((t + 1) * q * (k + 1) + 1) ^ 2)
    (ht : t + 1 ≤ B) (hq : q ≤ B) (hk : k + 1 ≤ B) :
    ℓ + k ≤ (4 * A + 1) * B ^ 6 := by
  have hpos : 0 < B := by omega
  have hcontrols : (t + 1) * q * (k + 1) ≤ B ^ 3 := by
    simpa [pow_succ] using Nat.mul_le_mul (Nat.mul_le_mul ht hq) hk
  have hplus : (t + 1) * q * (k + 1) + 1 ≤ 2 * B ^ 3 := by
    have := Nat.pow_pos hpos (n := 3)
    omega
  have hsq := Nat.pow_le_pow_left hplus 2
  have hk6 : k ≤ B ^ 6 := calc
    k ≤ B ^ 1 := by simpa using (show k ≤ B by omega)
    _ ≤ B ^ 6 := Nat.pow_le_pow_right hpos (by decide)
  calc
    ℓ + k ≤ A * (2 * B ^ 3) ^ 2 + B ^ 6 :=
      Nat.add_le_add (hprefix.trans (Nat.mul_le_mul_left _ hsq)) hk6
    _ = (4 * A + 1) * B ^ 6 := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, Nat.mul_comm A]

end VPVNP
end Computability
end OAI

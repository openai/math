import OAI.Computability.NearSquareRoot.Schedule

/-!
# Geometric schedule charges including unary slot indices

In round `s` every slot has `i + a + 1 = s`. Visiting those unary indices,
allocating a clock and erasing it can therefore add a quadratic term to the
round's aggregate budget. The geometric budgets absorb this term, together
with the controller's two head sweeps per round.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schedule

/-- The `k` remaining slots all belong to round `i+k`. -/
theorem slotCost_le_with_indices {charge : ℕ → ℕ → ℕ} {C : ℕ}
    (hc : ∀ i a, charge i a ≤ C * (2^a + i + a + 1)) (i k : ℕ) :
    slotCost charge i k + C ≤ C * (2^k + k * (i+k)) := by
  induction k generalizing i with
  | zero => simp [slotCost]
  | succ k ih =>
    have h := Nat.add_le_add (hc i k) (ih (i+1))
    simp only [slotCost, Nat.add_assoc] at h ⊢
    convert h using 1
    simp [pow_succ]
    ring

private theorem index_sweeps_le (s : ℕ) : s^2 + 2*s + 3 ≤ 3*2^s := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [pow_succ (2 : ℕ)]
    nlinarith

/-- The round includes the attempt charges and the `2*s` physical transitions
of the controller. The constant is independent of the round and the index. -/
theorem round_charge_le {charge : ℕ → ℕ → ℕ} {C : ℕ}
    (hc : ∀ i a, charge i a ≤ C * (2^a + i + a + 1)) (s : ℕ) :
    slotCost charge 0 s + 2*s ≤ 4*(C+1)*2^s := by
  have h := slotCost_le_with_indices hc 0 s
  simp only [Nat.zero_add, ← pow_two] at h
  have hs := index_sweeps_le s
  have hs' : s^2 ≤ 3*2^s := by omega
  nlinarith [Nat.mul_le_mul_left C hs']

/-- A fallback at index zero with a polynomial tick bound limits the largest
round (and hence both physical controller offsets) needed to see an answer. -/
theorem polynomial_fallback_round {σ α : Type*} {tick : σ → Tick σ α} {start : ℕ → σ}
    {t K n p : ℕ} {x : α} (hrun : tryFor tick t (start 0) = some x)
    (ht : t ≤ K * (n+1)^p) :
    ∃ s ≤ Nat.clog 2 K + p * Nat.clog 2 (n+1) + 1,
      (through (fun j b => tryFor tick b (start j)) s).isSome := by
  have hb : 1 < (2 : ℕ) := by decide
  refine ⟨Nat.clog 2 t + 1, Nat.add_le_add_right ((Nat.clog_le_iff_le_pow hb).2 ?_) 1, ?_⟩
  · rw [pow_add, Nat.mul_comm p, pow_mul]
    exact ht.trans (Nat.mul_le_mul (Nat.le_pow_clog hb K)
      (Nat.pow_le_pow_left (Nat.le_pow_clog hb (n+1)) p))
  · simpa using through_has_answer hrun

end Schedule

end NearSquareRoot
end Computability
end OAI

import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedFrameEncoding

/-! # Polynomial resource bounds for the full signed verifier clock -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

/-- On radius `r < n^100`, a per-tick polynomial in `n+r+2` stays polynomial in
`n` after summing the entire clock. This also accounts for guesses, the
initial row, and both occurrences of the final decoder check. -/
theorem verifierBudget_le {n h cost check P a C b : ℕ} (hn : 1 ≤ n)
    (stepCost : Fin (n^100) → ℕ) (hh : h ≤ 100*(n+2)^3)
    (hcheck : check ≤ P*(n+2)^a)
    (hstep : ∀ r, stepCost r ≤ C*(n + r.val + 2)^b)
    (hcost : cost ≤ Fintype.card (FrameWire n (n^100)) +
      (∑ r, stepCost r) + 2*(check+1)) :
    n + (h+n^100) + cost + 1 ≤
      (3000 + C*4^b + 2*P*3^a) * n^(100*(4+a+b)) := by
  let T := n^100
  let D := 100*(4+a+b)
  let Q := n^D
  have comp (k : ℕ) (hk : k ≤ D) : n^k ≤ Q := Nat.pow_le_pow_right hn hk
  have hnT : n ≤ T := by simpa [T] using Nat.pow_le_pow_right hn (show 1 ≤ 100 by decide)
  have hT : 1 ≤ T := hn.trans hnT
  have hQ : 1 ≤ Q := by simpa using comp 0 (Nat.zero_le D)
  have htQ : T ≤ Q := comp 100 (by dsimp [D]; omega)
  have h2Q : T^2 ≤ Q := by
    dsimp only [T]
    rw [← pow_mul]
    exact comp _ (by dsimp [D]; omega)
  have h3Q : n^3 ≤ Q := comp 3 (by dsimp [D]; omega)
  have haQ : n^a ≤ Q := comp a (by dsimp [D]; omega)
  have hbQ : T^(b+1) ≤ Q := by
    dsimp only [T]
    rw [← pow_mul]
    exact comp _ (by dsimp [D]; omega)
  have nsmall : n+2 ≤ 3*n := by omega
  have hguess : h ≤ 2700*Q := calc
    h ≤ 100*(3*n)^3 := hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left nsmall _))
    _ = 2700*n^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h3Q
  have hparse : check ≤ P*3^a*Q := calc
    check ≤ P*(3*n)^a := hcheck.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left nsmall _))
    _ = P*3^a*n^a := by rw [mul_pow, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ haQ
  have hf : Fintype.card (FrameWire n (n^100)) ≤ 23*Q := calc
    _ = 3+(n+1)+(n+1)*((2*T+1)*3) := frameWire_card _ _
    _ ≤ 3+(T+1)+(T+1)*((2*T+1)*3) := by gcongr
    _ ≤ 23*T^2 := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_left _ h2Q
  have hrs (r : Fin (n^100)) : n+r.val+2 ≤ 4*T := by
    have hr : r.val < T := r.isLt
    omega
  have hs : (∑ r, stepCost r) ≤ C*4^b*Q := calc
    _ ≤ ∑ _ : Fin (n^100), C*(4*T)^b :=
      Finset.sum_le_sum fun r _ => (hstep r).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hrs r) _))
    _ = T * (C*(4*T)^b) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rfl
    _ = C*4^b*T^(b+1) := by rw [mul_pow, pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hbQ
  have hnQ := hnT.trans htQ
  change n + (h + T) + cost + 1 ≤ (3000 + C*4^b + 2*P*3^a)*Q
  nlinarith only [hcost, hguess, hparse, hf, hs, hnQ, htQ, hQ]

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI

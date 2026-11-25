import OAI.Computability.BorderVNP.CoverDeckPackRunBounds

/-!
# A logarithmic count width for the physical pack selector

The entire sequence of comparisons fits in a word whose length is logarithmic
in the tile volume, candidate denominator, pack count, and raw cell bound.
The same width satisfies the upper-width condition of the sparse physical
histogram circuits after a polynomial increase in their size parameter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open PackedDeckCandidate

/-- A public working width depending only on numerical layout bounds. -/
def packWidth (n P k H : ℕ) := Nat.clog 2 ((n+P+k+H+2)^12)

private theorem maxCharge_lt (n P k H : ℕ) :
    let N := k*H+H
    let D := P*n
    let L := D*(k*H)+P*(n*N)
    N + L + 3*D*n^2*N^2 + 2*n^2*L*N < (n+P+k+H+2)^12 := by
  let s := n+P+k+H+2
  let N := k*H+H
  let D := P*n
  let L := D*(k*H)+P*(n*N)
  have hs : 2 ≤ s := by dsimp [s]; omega
  have hn : n ≤ s := by dsimp [s]; omega
  have hp : P ≤ s := by dsimp [s]; omega
  have hk : k+1 ≤ s := by dsimp [s]; omega
  have hh : H ≤ s := by dsimp [s]; omega
  have hN : N ≤ s^2 := by
    simpa [N,Nat.add_mul,pow_two] using Nat.mul_le_mul hk hh
  have hD : D ≤ s^2 := by simpa [D,pow_two] using Nat.mul_le_mul hp hn
  have hL : L ≤ 2*s^4 := by
    have h₁ := Nat.mul_le_mul hD ((Nat.le_add_right (k*H) H).trans hN)
    have h₂ := Nat.mul_le_mul hD hN
    calc
      L = D*(k*H)+D*N := by simp [L,D,Nat.mul_assoc]
      _ ≤ s^2*s^2+s^2*s^2 := Nat.add_le_add h₁ h₂
      _ = 2*s^4 := by rw [← pow_add,two_mul]
  have h₁ : 3*D*n^2*N^2 ≤ 3*s^8 := calc
    _ ≤ 3*s^2*s^2*(s^2)^2 := by gcongr
    _ = _ := by simp only [mul_assoc,← pow_mul,← pow_add]
  have h₂ : 2*n^2*L*N ≤ 4*s^8 := calc
    _ ≤ 2*s^2*(2*s^4)*s^2 := by gcongr
    _ = 4*(s^2*s^4*s^2) := by change _ = (2*2)*(s^2*s^4*s^2); ac_rfl
    _ = 4*s^8 := by rw [← pow_add,← pow_add]
  have h28 := Nat.pow_le_pow_right (show 0 < s by omega) (show 2 ≤ 8 by decide)
  have h48 := Nat.pow_le_pow_right (show 0 < s by omega) (show 4 ≤ 8 by decide)
  have hbase : 10 < s^4 := lt_of_lt_of_le (by decide : 10 < 2^4) (Nat.pow_le_pow_left hs 4)
  calc
    N+L+3*D*n^2*N^2+2*n^2*L*N ≤ 10*s^8 := by
      have hl := Nat.mul_le_mul_left 2 h48
      omega
    _ < s^4*s^8 := Nat.mul_lt_mul_of_pos_right hbase (pow_pos (by omega) _)
    _ = s^12 := (pow_add s 4 8).symm

/-- The denominator, raw counts, and every scalar in the compiled sequence
fit without truncation at the public width. -/
theorem packWidth_fits (n P k H : ℕ) :
    P < 2^packWidth n P k H ∧ H < 2^packWidth n P k H ∧ packRunWidth n P k H ≤ packWidth n P k H := by
  let s := n+P+k+H+2
  let w := packWidth n P k H
  have hs : 2 ≤ s := by dsimp [s]; omega
  have hp : s^12 ≤ 2^w := Nat.le_pow_clog (by decide) _
  have hbase : s ≤ s^12 := (pow_one s).symm.le.trans (Nat.pow_le_pow_right (by omega) (by decide : 1 ≤ 12))
  have hp' : P < 2^w := ((show P < s by dsimp [s]; omega).trans_le hbase).trans_le hp
  have hh : H < 2^w := ((show H < s by dsimp [s]; omega).trans_le hbase).trans_le hp
  refine ⟨hp',hh,?_⟩
  let N := k*H+H
  let D := P*n
  let L := D*(k*H)+P*(n*N)
  let M := N+L+3*D*n^2*N^2+2*n^2*L*N
  have hM : M < 2^w := (maxCharge_lt n P k H).trans_le hp
  change M.log2+1 ≤ w
  by_cases hz : M = 0
  · have hw : 0 < w := by
      by_contra! he
      have : w = 0 := by omega
      rw [this,pow_zero] at hp
      omega
    simpa [hz] using (show 1 ≤ w from hw)
  · exact (Nat.log2_lt hz).mpr hM

/-- The public word length is at most twelve times the logarithm of its
ordinary layout parameters. -/
theorem packWidth_le (n P k H : ℕ) : packWidth n P k H ≤ 12*Nat.clog 2 (n+P+k+H+2) := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) 12

/-- A common polynomial size parameter covers both physical rows and the
upper-width requirement of sparse histogram generation. -/
def packPadding (T n P k H : ℕ) := T+(n+P+k+H+2)^12

theorem packPadding_fits (T n P k H : ℕ) :
    T ≤ packPadding T n P k H ∧ packWidth n P k H ≤ Nat.clog 2 (packPadding T n P k H+1) := by
  refine ⟨Nat.le_add_right _ _,Nat.clog_mono_right _ ?_⟩
  dsimp [packPadding]
  omega

/-- The logarithm charged by the padded physical histogram stays logarithmic
in the original row count and layout parameters. -/
theorem packPadding_log (T n P k H : ℕ) :
    Nat.clog 2 (packPadding T n P k H+n+2) ≤ 13*Nat.clog 2 (T+n+P+k+H+3) := by
  let s := T+n+P+k+H+3
  have hs : 2 ≤ s := by dsimp [s]; omega
  have hbase : T+n+2 ≤ s := by dsimp [s]; omega
  have hp := Nat.pow_le_pow_left (show n+P+k+H+2 ≤ s by dsimp [s]; omega) 12
  have hlarge : s ≤ s^12 := (pow_one s).symm.le.trans (Nat.pow_le_pow_right (by omega) (by decide : 1 ≤ 12))
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  calc
    packPadding T n P k H+n+2 ≤ 2*s^12 := by dsimp [packPadding]; omega
    _ ≤ s*s^12 := Nat.mul_le_mul_right _ hs
    _ = s^13 := (pow_succ' s 12).symm
    _ ≤ 2^(13*Nat.clog 2 s) := by
      rw [mul_comm,pow_mul]
      exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) 13

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI

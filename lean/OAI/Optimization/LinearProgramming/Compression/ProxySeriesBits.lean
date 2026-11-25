import OAI.Optimization.LinearProgramming.Compression.ProxySeriesOperandBits

/-! Bit sizes at every visited state of the fixed truncated-logarithm RAM program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

private theorem series_entry_bits {s t : State ℚ} {B M : ℕ} {z : ℚ} (hz : 1 ≤ z)
    (hs : scalarBound B s) (hpc : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = z)
    (ht : runExactly logSeriesProgram s 9 = some t) : scalarBound (seriesRegisterBase B M) t := by
  let H := seriesRegisterBase B M
  have hb : B ≤ H := by dsimp [H, seriesRegisterBase]; omega
  have hH : 4 ≤ H := by dsimp [H, seriesRegisterBase]; omega
  have b0 : ratBits 0 ≤ H := by rw [show ratBits 0 = 3 by decide]; omega
  have b1 : ratBits 1 ≤ H := by rw [show ratBits 1 = 3 by decide]; omega
  have b2 : ratBits 2 ≤ H := by rw [show ratBits 2 = 4 by decide]; omega
  have O := logSeriesOperand_bits hz (M := M) (hd ▸ hs 0)
  have hp : ratBits (((z-1)/(z+1))*((z-1)/(z+1))) ≤ H := by
    simpa only [pow_two] using O.power 2 (by omega)
  have hne : z+1 ≠ 0 := by linarith
  simp [runExactly, step, logSeriesProgram, execInstr, State.putData, State.putIndex,
    Function.update, hpc, ho, hd, hne] at ht
  rw [← ht]
  repeat' apply update_bound
  all_goals first | exact fun j => (hs j).trans hb | exact b0 | exact b1 | exact b2 |
      exact O.minusOne | exact O.plusOne | exact O.argument | exact hp

private theorem series_round_bits {s t : State ℚ} {B M i : ℕ} {z : ℚ}
    (O : SeriesOperands z M (seriesRegisterBase B M))
    (hh : SeriesHead s ((z-1)/(z+1)) M i) (hs : scalarBound (seriesRegisterBase B M) s)
    (hi : i < M) (ht : runExactly logSeriesProgram s 7 = some t) :
    scalarBound (seriesRegisterBase B M) t := by
  obtain ⟨pc, go, hm, hi', h₂, h₃, h₄, h₅, h₆⟩ := hh
  let w := (z-1)/(z+1)
  let H := seriesRegisterBase B M
  have hne : 2*(i:ℚ)+1 ≠ 0 := by positivity
  have hterm : ratBits (s.data 3 / (2*(i:ℚ)+1)) ≤ H := by
    rw [h₃]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
      O.term (2*i+1) (by omega)
  have hsum : ratBits (s.data 5 + s.data 3 / (2*(i:ℚ)+1)) ≤ H := by
    rw [h₅, h₃]
    simpa [oddPartial, Finset.sum_range_succ] using O.sum (i+1) (by omega)
  have hpow : ratBits (s.data 3 * s.data 4) ≤ H := by
    rw [h₃, h₄, ← pow_add]
    exact O.power _ (by omega)
  have hden : ratBits (2*(i:ℚ)+1+2) ≤ H := by
    have h := O.oddDenominator (2*i+1+2) (by omega)
    exact_mod_cast h
  simp [runExactly, step, logSeriesProgram, execInstr, State.putData, State.putIndex,
    Function.update, pc, go, hm, hi', h₂, h₆, hne, hi] at ht
  rw [← ht]
  repeat' apply update_bound
  all_goals first | exact hs | exact hterm | exact hsum | exact hpow | exact hden

/-- The `7M+12`-step series program preserves polynomial encoding lengths at
every instruction, including the transient powers and divisions. -/
theorem logSeriesProgram_scalarBound {z : ℚ} (hz : 1 ≤ z) (M B : ℕ) (s : State ℚ)
    (hpc : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = z) (hm : s.index 0 = M)
    (hbound : scalarBound B s) {n : ℕ} (hn : n ≤ 9+7*M+3) {t : State ℚ}
    (ht : runExactly logSeriesProgram s n = some t) :
    scalarBound (10^9 * seriesRegisterBase B M) t := by
  let H := seriesRegisterBase B M
  have hH : 4 ≤ H := by dsimp [H, seriesRegisterBase]; omega
  have hconst (d : ℕ) (r : ℚ) (h : Instr.const d r ∈ logSeriesProgram) : ratBits r ≤ H := by
    have h0 : ratBits 0 = 3 := by decide
    have h1 : ratBits 1 = 3 := by decide
    have h2 : ratBits 2 = 4 := by decide
    simp [logSeriesProgram] at h
    grind
  have short {u v : State ℚ} {j : ℕ} (hj : j ≤ 9) (hu : scalarBound H u)
      (hv : runExactly logSeriesProgram u j = some v) : scalarBound (10^9 * H) v := by
    have h := scalarSteps_bound hH hconst hu hv
    have hp := Nat.pow_le_pow_right (n := 10) (by decide) hj
    intro l; exact (h l).trans (Nat.mul_le_mul_right _ hp)
  by_cases hentry : n ≤ 9
  · exact short hentry (fun j => (hbound j).trans (by dsimp [H, seriesRegisterBase]; omega)) ht
  let w := (z-1)/(z+1)
  have O := logSeriesOperand_bits hz (M := M) (hd ▸ hbound 0)
  have heads (i : ℕ) (hi : i ≤ M) :
      ∃ a, runExactly logSeriesProgram s (9+7*i) = some a ∧
        SeriesHead a w M i ∧ scalarBound H a := by
    induction i with
    | zero =>
      obtain ⟨a, ha, hh⟩ := series_init z M hz s hpc ho hd hm
      exact ⟨a, by simpa only [Nat.mul_zero, Nat.add_zero] using ha, hh,
        series_entry_bits hz hbound hpc ho hd ha⟩
    | succ i ih =>
      obtain ⟨a, ha, hh, hb⟩ := ih (by omega)
      obtain ⟨b, hr, hb'⟩ := series_body hh (by omega)
      refine ⟨b, ?_, hb', series_round_bits O hh hb (by omega) hr⟩
      rw [show 9+7*(i+1) = 9+7*i+7 by omega, runExactly_add_series, ha, Option.bind_some]
      exact hr
  let i := min M ((n-9)/7)
  obtain ⟨a, ha, _, hb⟩ := heads i (min_le_left _ _)
  let j := n-(9+7*i)
  have hsplit : n = 9+7*i+j := by dsimp [j,i]; omega
  have hj : j ≤ 9 := by dsimp [j,i]; omega
  rw [hsplit, runExactly_add_series, ha, Option.bind_some] at ht
  exact short hj hb ht

end Compression
end LinearProgramming
end Optimization
end OAI

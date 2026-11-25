import OAI.Optimization.LinearProgramming.Compression.ProxySeriesCost
import OAI.Optimization.LinearProgramming.Compression.ProxyRegisterBits

/-! Uniform rational register bounds throughout dyadic digit construction. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer
open OAI.Optimization.LinearProgramming.PrimalDual (ratBits_mul_le ratBits_sub_le ratBits_inv_le ratBits_neg)

private def gridBound (B M : ℕ) := 12 + 4 * (B + M + 3)

private theorem gridEntry_bound {s t : State ℚ} {B M : ℕ} (hs : scalarBound B s)
    (hpc : s.pc = 0) (ho : s.output = none) (ht : runExactly dyadicGridProgram s 7 = some t) :
    scalarBound (gridBound B M) t := by
  have unchanged : RegBound (gridBound B M) s.data := fun j => (hs j).trans (by dsimp [gridBound]; omega)
  have h0 : ratBits 0 ≤ gridBound B M := by
    rw [show ratBits 0 = 3 by decide]; dsimp [gridBound]; omega
  have h1 : ratBits 1 ≤ gridBound B M := by
    rw [show ratBits 1 = 3 by decide]; dsimp [gridBound]; omega
  have h2 : ratBits 2 ≤ gridBound B M := by
    rw [show ratBits 2 = 4 by decide]; dsimp [gridBound]; omega
  simp [runExactly, step, dyadicGridProgram, execInstr, State.putData, State.putIndex,
    Function.update, hpc, ho] at ht
  rw [← ht]
  apply update_bound _ _ (unchanged 0)
  apply update_bound _ _ h1
  apply update_bound _ _ h0
  apply update_bound _ _ h2
  exact update_bound unchanged _ h1

private theorem gridRound_bound {q : ℚ} {s t : State ℚ} {B M i : ℕ} (hq : ratBits q ≤ B)
    (hh : GridHead s q M i) (hb : scalarBound (gridBound B M) s) (hi : i < M)
    (ht : runExactly dyadicGridProgram s 13 = some t) : scalarBound (gridBound B M) t := by
  obtain ⟨pc, go, hm, hi', hw, h₁, h₂, h₃, h₄, h₅, _⟩ := hh
  let p := (dyadicSearch (dyadicTest q) i).1
  have hp : p < 2 ^ i := dyadicSearch_numerator_lt _ _
  have hn (j : ℕ) (hj : j ≤ 2 ^ (i+1)) : ratBits (j : ℚ) ≤ gridBound B M :=
    (natCast_ratBits_le hj).trans (by dsimp [gridBound]; omega)
  have hp2 : p*2 ≤ 2 ^ (i+1) := by rw [pow_succ]; omega
  have hpp : p*2+1 ≤ 2 ^ (i+1) := by rw [pow_succ]; omega
  have h0 : ratBits 0 ≤ gridBound B M := by
    rw [show ratBits 0 = 3 by decide]; dsimp [gridBound]; omega
  have h1 : ratBits 1 ≤ gridBound B M := by
    rw [show ratBits 1 = 3 by decide]; dsimp [gridBound]; omega
  have h3 : ratBits (s.data 3 * 2) ≤ gridBound B M := by
    rw [h₃]; simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn _ hp2
  have h6 : ratBits (s.data 3 * 2 + 1) ≤ gridBound B M := by
    rw [h₃]; simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hn _ hpp
  have h4 : ratBits (s.data 4 * 2) ≤ gridBound B M := by
    rw [h₄, ← pow_succ]
    exact_mod_cast hn (2 ^ (i+1)) le_rfl
  have h5 : ratBits (s.data 5 * 2) ≤ gridBound B M := by
    rw [h₅, mul_right_comm, ← pow_succ]
    have hw' : ratBits ((2 : ℚ) ^ (i+1)) ≤ (i+1)+3 := by exact_mod_cast natCast_ratBits_le (e := i+1) le_rfl
    have hmul := ratBits_mul_le ((2:ℚ)^(i+1)) q
    dsimp [gridBound]; omega
  by_cases hc : s.data 5 * 2 < s.data 3 * 2 + 1 <;>
    simp (config := { maxSteps := 50000 }) [runExactly, step, dyadicGridProgram, execInstr,
      State.putData, State.putIndex, Function.update, pc, go, hm, hi', hw, h₁, h₂, hi, hc] at ht
  all_goals
    rw [← ht]
    repeat' apply update_bound
    all_goals first | exact hb | exact h0 | exact h1 | exact h3 | exact h4 | exact h5 | exact h6

/-- Uniform bound for every register in every prefix of the fixed dyadic search,
starting with arbitrary bounded input and scratch registers. -/
theorem dyadicGridProgram_scalarBound (q : ℚ) (M B : ℕ) (s : State ℚ)
    (hpc : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = q) (hm : s.index 0 = M)
    (hbound : scalarBound B s) {n : ℕ} (hn : n ≤ 7 + 13*M + 3) {t : State ℚ}
    (ht : runExactly dyadicGridProgram s n = some t) :
    scalarBound (10 ^ 13 * (12 + 4 * (B + M + 3))) t := by
  let H := gridBound B M
  have hH : 4 ≤ H := by dsimp [H, gridBound]; omega
  have hconst (d : ℕ) (r : ℚ) (h : Instr.const d r ∈ dyadicGridProgram) : ratBits r ≤ H := by
    have h0 : ratBits 0 = 3 := by decide
    have h1 : ratBits 1 = 3 := by decide
    have h2 : ratBits 2 = 4 := by decide
    simp [dyadicGridProgram] at h
    grind
  have short {u v : State ℚ} {j : ℕ} (hj : j ≤ 13) (hu : scalarBound H u)
      (hv : runExactly dyadicGridProgram u j = some v) : scalarBound (10^13 * H) v := by
    have h := scalarSteps_bound hH hconst hu hv
    have hp := Nat.pow_le_pow_right (n := 10) (by decide) hj
    intro l; exact (h l).trans (Nat.mul_le_mul_right _ hp)
  by_cases hentry : n ≤ 7
  · exact short (by omega) (fun j => (hbound j).trans (by dsimp [H, gridBound]; omega)) ht
  have heads (i : ℕ) (hi : i ≤ M) :
      ∃ a, runExactly dyadicGridProgram s (7 + 13 * i) = some a ∧
        GridHead a q M i ∧ scalarBound H a := by
    induction i with
    | zero =>
      obtain ⟨a, ha, hh⟩ := grid_init q M s hpc ho hd hm
      exact ⟨a, by simpa only [Nat.mul_zero, Nat.add_zero] using ha, hh, gridEntry_bound hbound hpc ho ha⟩
    | succ i ih =>
      obtain ⟨a, ha, hh, hb⟩ := ih (by omega)
      obtain ⟨b, hr, hb'⟩ := grid_body hh (by omega)
      refine ⟨b, ?_, hb', gridRound_bound (hd ▸ hbound 0) hh hb (by omega) hr⟩
      rw [show 7 + 13*(i+1) = 7+13*i+13 by omega, runExactly_add_series, ha, Option.bind_some]
      exact hr
  let i := min M ((n-7)/13)
  obtain ⟨a, ha, _, hb⟩ := heads i (min_le_left _ _)
  let j := n-(7+13*i)
  have hsplit : n = 7 + 13*i + j := by dsimp [j,i]; omega
  have hj : j ≤ 13 := by dsimp [j,i]; omega
  rw [hsplit, runExactly_add_series, ha, Option.bind_some] at ht
  exact short hj hb ht

end Compression
end LinearProgramming
end Optimization
end OAI

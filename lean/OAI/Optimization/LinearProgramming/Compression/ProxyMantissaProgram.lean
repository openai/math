import OAI.Optimization.LinearProgramming.Compression.ProxyProgramFrame
import OAI.Optimization.LinearProgramming.Compression.ProxyRelocation

/-! The complete fixed scalar RAM program for one normalized small logarithm.
It evaluates the same odd series kernel twice and then emits the dyadic bits. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

private def mantissaInit : Program :=
  [.addrCopy 3 0, .addrConst 4 0, .addrConst 5 1] ++ List.replicate 6 (.incr 0 0)

private def afterSeries : Program := [
  .branchAddrLT 4 5 27 31, .copy 9 0, .const 0 2, .incr 4 4, .jump 9,
  .div 0 9 0, .addrCopy 0 3, .incr 0 0, .incr 0 0]

/-- The input consists of the scalar mantissa and a constructed natural precision
counter. The first instance of the series code returns to the same code with
input two; the second passes the quotient to the grid code. -/
def mantissaProgram : Program := mantissaInit ++
  (logSeriesProgram.take 17).map (rebaseInstr 9) ++ afterSeries ++
  dyadicGridProgram.map (rebaseInstr 35)

theorem series_lookup (i : ℕ) (op : Instr) (h : logSeriesProgram[i]? = some op)
    (hh : false = true ∨ ∀ tag, op ≠ .halt tag) :
    mantissaProgram[9 + i]? = some (rebaseInstr 9 op) := by
  have hi : i < 18 := by
    by_contra! hn
    have hsize : logSeriesProgram.length ≤ i := by simpa [logSeriesProgram] using hn
    rw [List.getElem?_eq_none hsize] at h; cases h
  interval_cases i <;> simp [logSeriesProgram] at h <;> subst op <;>
    first | rfl | simp at hh

theorem grid_lookup (i : ℕ) (op : Instr) (h : dyadicGridProgram[i]? = some op)
    (_ : true = true ∨ ∀ tag, op ≠ .halt tag) :
    mantissaProgram[35 + i]? = some (rebaseInstr 35 op) := by
  have hi : i < 25 := by
    by_contra! hn
    have hsize : dyadicGridProgram.length ≤ i := by simpa [dyadicGridProgram] using hn
    rw [List.getElem?_eq_none hsize] at h; cases h
  interval_cases i <;> simp [dyadicGridProgram] at h <;> subst op <;> rfl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem mantissa_setup (z : K) (k : ℕ) (s : State K) (hpc : s.pc = 0)
    (hgo : s.output = none) (hd : s.data 0 = z) (hm : s.index 0 = k) :
    ∃ u : State K, runExactly mantissaProgram s 9 = some u ∧
      u.pc = 9 ∧ u.output = none ∧ u.data 0 = z ∧ u.index 0 = k+6 ∧
      u.index 3 = k ∧ u.index 4 = 0 ∧ u.index 5 = 1 ∧ PreservesRegisters (k+12) 6 s u := by
  simp [runExactly, step, mantissaProgram, mantissaInit, execInstr, State.putIndex,
    Function.update, List.replicate_succ, hpc, hgo, hd, hm]
  constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

/-- Execute the common series region and leave the live machine at its dispatch
instruction, retaining all caller slots. -/
theorem run_series_region (z : K) (M : ℕ) (hz : 1 ≤ z) (a : State K)
    (ha : a.pc = 9) (ho : a.output = none) (hd : a.data 0 = z) (hm : a.index 0 = M) :
    ∃ u, runExactly mantissaProgram a (9 + 7*M + 2) = some u ∧ u.pc = 26 ∧
      u.output = none ∧ u.data 0 = logTruncation z M ∧ u.data 9 = a.data 9 ∧
      u.index 3 = a.index 3 ∧ u.index 4 = a.index 4 ∧ u.index 5 = a.index 5 ∧
      u.index 0 = a.index 0 ∧ PreservesRegisters 8 2 a u := by
  let s := {a with pc := 0}
  have hback : stateAt 9 s = a := by cases a; simp_all [s, stateAt]
  obtain ⟨v, hv, hpc, hgo, hans⟩ := series_run_until_halt hz M s rfl ho hd hm
  have hr := relocate_run 9 false series_lookup hv (Or.inr hgo)
  rw [hback] at hr
  obtain ⟨hd9, hi3, hi4, hi5, hi0⟩ := series_caller_registers hv
  exact ⟨stateAt 9 v, hr, by simp [stateAt, hpc], hgo, hans, hd9, hi3, hi4, hi5, hi0,
    by change PreservesRegisters 8 2 s v; exact logSeriesProgram_frame hv⟩

theorem run_first_return (s : State K) (k : ℕ) (ans : K) (hpc : s.pc = 26)
    (hgo : s.output = none) (hans : s.data 0 = ans) (h3 : s.index 3 = k)
    (h4 : s.index 4 = 0) (h5 : s.index 5 = 1) (h0 : s.index 0 = k + 6) :
    ∃ u, runExactly mantissaProgram s 5 = some u ∧ u.pc = 9 ∧ u.output = none ∧
      u.data 0 = 2 ∧ u.data 9 = ans ∧ u.index 0 = k+6 ∧
      u.index 3 = k ∧ u.index 4 = 1 ∧ u.index 5 = 1 ∧ PreservesRegisters (k+12) 6 s u := by
  simp [runExactly, step, mantissaProgram, mantissaInit, logSeriesProgram, afterSeries,
    rebaseInstr, execInstr, State.putData, State.putIndex, Function.update,
    hpc, hgo, hans, h3, h4, h5, h0]
  constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

theorem run_second_return (s : State K) (k : ℕ) (a b : K) (hb : b ≠ 0)
    (hpc : s.pc = 26) (hgo : s.output = none) (h0 : s.data 0 = b) (h9 : s.data 9 = a)
    (h3 : s.index 3 = k) (h4 : s.index 4 = 1) (h5 : s.index 5 = 1) :
    ∃ u, runExactly mantissaProgram s 5 = some u ∧ u.pc = 35 ∧ u.output = none ∧
      u.data 0 = a / b ∧ u.index 0 = k + 2 ∧ PreservesRegisters (k+12) 6 s u := by
  simp [runExactly, step, mantissaProgram, mantissaInit, logSeriesProgram, afterSeries,
    rebaseInstr, execInstr, State.putData, State.putIndex, Function.update,
    hpc, hgo, h0, h9, h3, h4, h5, hb]
  constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

theorem run_grid_region (q : K) (M : ℕ) (a : State K)
    (hpc : a.pc = 35) (ho : a.output = none) (hd : a.data 0 = q) (hm : a.index 0 = M) :
    ∃ u, runExactly mantissaProgram a (7 + 13*M + 2) = some u ∧
      u.pc = 59 ∧ u.output = none ∧ u.data 0 = ((dyadicSearch (dyadicTest q) M).1 : K) / 2 ^ M ∧
      (∀ j < M, u.data (8+j) = ((gridDigit q j).toNat : K)) ∧ PreservesRegisters (8+M) 3 a u := by
  let s := {a with pc := 0}
  have hback : stateAt 35 s = a := by cases a; simp_all [s, stateAt]
  obtain ⟨v, hv, hpc', hgo, hans, hbits, hframe⟩ := grid_run_until_halt q M s rfl ho hd hm
  have hr := relocate_run 35 true grid_lookup hv (Or.inl rfl)
  rw [hback] at hr
  exact ⟨stateAt 35 v, hr, by simp [stateAt, hpc'], hgo, hans, hbits, hframe⟩

private theorem joinRuns {p : Program} {a b c : State K} {i j : ℕ}
    (ha : runExactly p a i = some b) (hb : runExactly p b j = some c) :
    runExactly p a (i + j) = some c := by
  rw [runExactly_add_series, ha, Option.bind_some]
  exact hb

/-- Entry and return contract for linking into a larger program. The kernel
returns just before its halt and preserves every scalar at or above `k+12`
and every address at or above 6. -/
theorem mantissaProgram_run_until_halt {z : K} (hz : 1 ≤ z) (k : ℕ) (s : State K)
    (hpc : s.pc = 0) (hgo : s.output = none) (hd : s.data 0 = z) (hm : s.index 0 = k) :
    ∃ u, runExactly mantissaProgram s (27*k+160) = some u ∧ u.pc = 59 ∧ u.output = none ∧
      u.data 0 = ((mantissaGridNumerator z k).1 : K) / 2 ^ (k+2) ∧
      (∀ j < k+2, u.data (8+j) =
        ((gridDigit (logTruncation z (k+6) / logTruncation (2 : K) (k+6)) j).toNat : K)) ∧
      PreservesRegisters (k+12) 6 s u := by
  let M := k + 6
  let a := logTruncation z M
  let b := logTruncation (2 : K) M
  have hb : b ≠ 0 := by
    apply ne_of_gt
    change 0 < 2 * ∑ j ∈ Finset.range M,
      (((2 : K) - 1) / (2 + 1)) ^ (2*j+1) / (2 * (j:K)+1)
    apply mul_pos (by norm_num)
    apply Finset.sum_pos'
    · intro j _; positivity
    · exact ⟨0, Finset.mem_range.mpr (by dsimp [M]; omega), by norm_num⟩
  obtain ⟨u₀, e₀, pc₀, o₀, d₀, m₀, k₀, f₀, n₀, F₀⟩ := mantissa_setup z k s hpc hgo hd hm
  obtain ⟨u₁, e₁, pc₁, o₁, d₁, _, k₁, f₁, n₁, m₁, F₁⟩ :=
    run_series_region z M hz u₀ pc₀ o₀ d₀ m₀
  obtain ⟨u₂, e₂, pc₂, o₂, d₂, s₂, m₂, k₂, f₂, n₂, F₂⟩ :=
    run_first_return u₁ k a pc₁ o₁ d₁ (k₁.trans k₀) (f₁.trans f₀) (n₁.trans n₀) (m₁.trans m₀)
  obtain ⟨u₃, e₃, pc₃, o₃, d₃, s₃, k₃, f₃, n₃, _, F₃⟩ :=
    run_series_region 2 M (by norm_num) u₂ pc₂ o₂ d₂ m₂
  obtain ⟨u₄, e₄, pc₄, o₄, d₄, m₄, F₄⟩ :=
    run_second_return u₃ k a b hb pc₃ o₃ d₃ (s₃.trans s₂) (k₃.trans k₂) (f₃.trans f₂) (n₃.trans n₂)
  obtain ⟨u₅, e₅, pc₅, o₅, d₅, bits, F₅⟩ := run_grid_region (a / b) (k+2) u₄ pc₄ o₄ d₄ m₄
  have hrun := joinRuns (joinRuns (joinRuns (joinRuns (joinRuns e₀ e₁) e₂) e₃) e₄) e₅
  have hlen : 9 + (9 + 7*M + 2) + 5 + (9 + 7*M + 2) + 5 + (7 + 13*(k+2) + 2) =
      27*k + 160 := by dsimp [M]; omega
  rw [hlen] at hrun
  have F₁' := F₁.weaken (d' := k+12) (a' := 6) (by omega) (by decide)
  have F₃' := F₃.weaken (d' := k+12) (a' := 6) (by omega) (by decide)
  have F₅' := F₅.weaken (d' := k+12) (a' := 6) (by omega) (by decide)
  exact ⟨u₅, hrun, pc₅, o₅, d₅, bits, F₀.trans (F₁'.trans (F₂.trans (F₃'.trans (F₄.trans F₅'))))⟩

/-- The complete normalized logarithm program halts in exactly `27k+161`
RAM steps over every ordered field. Its only divisions are by nonzero scalars. -/
theorem mantissaProgram_run {z : K} (hz : 1 ≤ z) (k : ℕ) :
    ∃ t : Fin (27*k+161+1) → State K,
      Trace mantissaProgram (start [k] [z]) (27*k+161) t ∧
      (t (Fin.last _)).output = some 0 ∧
      (t (Fin.last _)).data 0 = ((mantissaGridNumerator z k).1 : K) / 2 ^ (k+2) ∧
      ∀ j < k+2, (t (Fin.last _)).data (8+j) =
        ((gridDigit (logTruncation z (k+6) / logTruncation (2 : K) (k+6)) j).toNat : K) := by
  obtain ⟨u, hu, hp, ho, hd, bits, _⟩ := mantissaProgram_run_until_halt hz k
    (start [k] [z]) rfl rfl rfl rfl
  let v := {u with output := some 0}
  have hv : step mantissaProgram u = some v := by
    simp [step, hp, ho, mantissaProgram, mantissaInit, logSeriesProgram, dyadicGridProgram,
      afterSeries, rebaseInstr, execInstr, v]
  have hend : runExactly mantissaProgram (start [k] [z]) (27*k+161) = some v := by
    change (runExactly mantissaProgram (start [k] [z]) (27*k+160)).bind (step mantissaProgram) = _
    rw [hu, Option.bind_some]; exact hv
  obtain ⟨t, htrace, hlast⟩ := (runExactly_iff_trace _).mp hend
  exact ⟨t, htrace, by rw [hlast], hlast ▸ hd, hlast ▸ bits⟩

/-- Over rational input the register value is a certified dyadic approximation
to the real base-two logarithm, with all its digits available in registers. -/
theorem mantissaProgram_exec {z : ℚ} (hz : 1 ≤ z) (hz' : z ≤ 2) (k : ℕ) :
    ∃ t : Fin (27*k+161+1) → State ℚ,
      Trace mantissaProgram (start [k] [z]) (27*k+161) t ∧
      (t (Fin.last _)).output = some 0 ∧
      (t (Fin.last _)).data 0 = ((mantissaGridNumerator z k).1 : ℚ) / 2 ^ (k+2) ∧
      (∀ j < k+2, (t (Fin.last _)).data (8+j) =
        ((gridDigit (logTruncation z (k+6) / logTruncation (2 : ℚ) (k+6)) j).toNat : ℚ)) ∧
      |(((t (Fin.last _)).data 0 : ℚ) : ℝ) - Real.logb 2 (z : ℝ)| < (1 / 2 : ℝ) ^ k / 2 := by
  obtain ⟨t, ht, ho, hd, hb⟩ := mantissaProgram_run hz k
  refine ⟨t, ht, ho, hd, hb, ?_⟩
  rw [hd]
  push_cast
  exact mantissaGrid_error hz hz' k

end Compression
end LinearProgramming
end Optimization
end OAI

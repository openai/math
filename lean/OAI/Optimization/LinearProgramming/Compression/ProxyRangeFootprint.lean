import OAI.Optimization.LinearProgramming.Compression.ProxyRangeFrame
import OAI.Optimization.LinearProgramming.Compression.ProxyProgramFrame

/-! The range kernel uses at most one stack slot per unit of initial fuel. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer RangeKernel

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- At PC 14 the pointer has advanced and the matching fuel debit is the next
instruction. The store at PC 12 is reached only with positive remaining fuel. -/
private def StackWithin (cap : ℕ) (s : State K) : Prop :=
  9 ≤ s.pc ∧ s.index 3 + s.index 0 ≤ cap + (if s.pc = 14 then 1 else 0) ∧
  ((s.pc = 12 ∨ s.pc = 13 ∨ s.pc = 14) → 0 < s.index 0)

private theorem range_step_within {cap : ℕ} (hcap : 8 ≤ cap) {s t : State K}
    (hh : StackWithin cap s) (hr : step logRangeProgram s = some t) :
    StackWithin cap t ∧ ∀ j, cap ≤ j → t.data j = s.data j := by
  have hgo : s.output = none := by
    cases h : s.output with
    | none => rfl
    | some o => simp [step, h] at hr
  have hlt : s.pc < 27 := by
    by_contra! h
    have hl : logRangeProgram.length ≤ s.pc := by simpa [logRangeProgram] using h
    simp [step, hgo, List.getElem?_eq_none hl] at hr
  obtain ⟨hlo, hmass, hguard⟩ := hh
  interval_cases hpc : s.pc <;> simp at hmass hguard <;>
    simp [step, hpc, hgo, logRangeProgram, execInstr, State.putData, State.putIndex] at hr
  all_goals
    rw [← hr]
    constructor
    · simp [StackWithin, Function.update]
      all_goals first | omega | (split_ifs <;> omega)
    · intro j hj
      simp (disch := omega) only [Function.update_of_ne]

private theorem range_from_scan_frame {cap : ℕ} (hcap : 8 ≤ cap) {s t : State K} {n : ℕ}
    (hs : StackWithin cap s) (hr : runExactly logRangeProgram s n = some t) :
    StackWithin cap t ∧ ∀ j, cap ≤ j → t.data j = s.data j := by
  induction n generalizing t with
  | zero =>
    change some s = some t at hr
    cases Option.some.inj hr
    exact ⟨hs, fun _ _ => rfl⟩
  | succ n ih =>
    change (runExactly logRangeProgram s n).bind (step logRangeProgram) = some t at hr
    cases hu : runExactly logRangeProgram s n with
    | none => simp [hu] at hr
    | some u =>
      obtain ⟨hh, hf⟩ := ih hu
      obtain ⟨hh', hf'⟩ := range_step_within hcap hh (by simpa [hu] using hr)
      exact ⟨hh', fun j hj => (hf' j hj).trans (hf j hj)⟩

private theorem range_before_scan_frame {s t : State K} {mag : K} (hm : 0 < mag)
    (hpc : s.pc = 0) (hgo : s.output = none) (hd : s.data 0 = mag) {n : ℕ} (hn : n ≤ 9)
    (hr : runExactly logRangeProgram s n = some t) :
    ∀ j, 8 ≤ j → t.data j = s.data j := by
  intro j hj
  interval_cases n <;> by_cases h : mag < 1 <;>
    simp [runExactly, step, logRangeProgram, execInstr, State.putData, State.putIndex,
      hpc, hgo, hd, hm.ne', h, Function.update] at hr
  all_goals rw [← hr] <;> simp (disch := omega) only [Function.update_of_ne]

/-- Every legal prefix, including the pre-halt dispatch, preserves all caller
scalars at addresses `8+fuel` and above and every caller index from 4 up. -/
theorem logRangeProgram_frame (fuel : ℕ) {mag : K} (hm : 0 < mag) (s : State K)
    (hp : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = mag) (hf : s.index 0 = fuel)
    {n : ℕ} {t : State K} (ht : runExactly logRangeProgram s n = some t) :
    PreservesRegisters (8+fuel) 4 s t := by
  refine ⟨?_, fun j hj => range_preserves_index ht hj⟩
  intro j hj
  obtain ⟨i, hi, u, hu, hscan⟩ := scan_init mag hm fuel s hp ho hd hf
  have hj8 : 8 ≤ j := by omega
  by_cases h : n ≤ i
  · exact range_before_scan_frame hm hp ho hd (by omega) ht j hj8
  · have hu' := range_before_scan_frame hm hp ho hd hi hu j hj8
    obtain ⟨pc, _, _, _, _, _, _, hm', _, _, hptr⟩ := hscan
    have hwithin : StackWithin (8+fuel) u := by simp [StackWithin, pc, hm', hptr]
    rw [show n = i+(n-i) by omega, runExactly_add_series, hu, Option.bind_some] at ht
    exact ((range_from_scan_frame (by omega) hwithin ht).2 j hj).trans hu'

end Compression
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Compression.ProxyRangeMachine
import Mathlib.Tactic.IntervalCases

/-! Composition interface for the adaptive range-search kernel. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem writes_halt {s t : State K} {op : Instr} {tag : ℕ}
    (hs : s.output = none) (h : execInstr op s = some t) (ht : t.output = some tag) :
    op = .halt tag ∧ t.data = s.data ∧ t.index = s.index := by
  cases op <;> simp only [execInstr] at h
  all_goals try split at h
  all_goals first | contradiction | (cases h; simp_all [State.putData, State.putIndex])

/-- In any legal trace that halts, the last instruction is the matching halt; the
scalar and address banks are identical immediately before and after it. -/
theorem live_state_before_halt {p : Program} {s : State K} (hs : s.output = none)
    {n : ℕ} {t : Fin (n+1) → State K} (h : Trace p s n t)
    {tag : ℕ} (hout : (t (Fin.last _)).output = some tag) :
    ∃ k < n, ∃ u, runExactly p s k = some u ∧ u.output = none ∧
      p[u.pc]? = some (.halt tag) ∧ u.data = (t (Fin.last _)).data ∧
      u.index = (t (Fin.last _)).index := by
  have hend := runExactly_of_trace h (Fin.last n)
  change runExactly p s n = some (t (Fin.last _)) at hend
  cases n with
  | zero =>
    change some s = some (t (Fin.last 0)) at hend
    rw [← Option.some.inj hend, hs] at hout
    contradiction
  | succ n =>
    change (runExactly p s n).bind (step p) = some (t (Fin.last _)) at hend
    cases hu : runExactly p s n with
    | none => simp [hu] at hend
    | some u =>
      have hstep : step p u = some (t (Fin.last _)) := by simpa [hu] using hend
      cases hgo : u.output with
      | some _ => simp [step, hgo] at hstep
      | none =>
        cases hop : p[u.pc]? with
        | none => simp [step,hgo,hop] at hstep
        | some op =>
          have hi : execInstr op u = some (t (Fin.last _)) := by simpa [step,hgo,hop] using hstep
          obtain ⟨rfl,hd,ha⟩ := writes_halt hgo hi hout
          exact ⟨n,Nat.lt_succ_self _,u,hu,hgo,hop,hd.symm,ha.symm⟩

private theorem range_halt_pc {j tag : ℕ} (h : logRangeProgram[j]? = some (.halt tag)) :
    j = if tag = 0 then 18 else 11 := by
  have hj : j < 27 := by
    by_contra! hn
    have hsz : logRangeProgram.length ≤ j := by simpa [logRangeProgram] using hn
    rw [List.getElem?_eq_none hsz] at h
    contradiction
  interval_cases j <;> simp [logRangeProgram] at h <;> simp_all
  omega

/-- The range search stops at a live dispatch point. Its caller may reuse the result
registers and continue to the mantissa or symbolic branch without executing a halt. -/
theorem range_run_until_halt (fuel : ℕ) {mag : K} (hm : 0 < mag) (a : State K)
    (hpc : a.pc = 0) (hgo : a.output = none) (hd : a.data 0 = mag) (hf : a.index 0 = fuel) :
    ∃ ell < 16*fuel+14, ∃ u, runExactly logRangeProgram a ell = some u ∧ u.output = none ∧
      (match rangeAnswer fuel (normalizedRangeInput mag) 2 with
       | none => u.pc = 11
       | some (e,q) => u.pc = 18 ∧ u.data 0 = normalizedRangeInput mag ∧
           u.data 3 = q ∧ u.data 4 = (e : K)) := by
  obtain ⟨n,hn,t,ht,hret⟩ := logRangeProgram_trace_from fuel hm a hpc hgo hd hf
  cases he : rangeAnswer fuel (normalizedRangeInput mag) 2 with
  | none =>
    rw [he] at hret
    obtain ⟨k,hk,u,hu,ho,hhalt,_,_⟩ := live_state_before_halt hgo ht hret
    exact ⟨k,hk.trans_le hn,u,hu,ho,by simpa using range_halt_pc hhalt⟩
  | some pair =>
    rcases pair with ⟨e,q⟩
    rw [he] at hret
    obtain ⟨hout,h₀,h₃,h₄⟩ := hret
    obtain ⟨k,hk,u,hu,ho,hhalt,hdata,_⟩ := live_state_before_halt hgo ht hout
    exact ⟨k,hk.trans_le hn,u,hu,ho,by simpa using range_halt_pc hhalt,
      hdata ▸ h₀, hdata ▸ h₃, hdata ▸ h₄⟩

private def leavesIndex (j : ℕ) : Instr → Prop
  | .addrConst d _ | .addrCopy d _ | .incr d _ | .decr d _ | .addrLoad d _ => j ≠ d
  | .addrStore _ _ => False
  | _ => True

private theorem keep_index {j : ℕ} {op : Instr} {a b : State K}
    (hs : leavesIndex j op) (he : execInstr op a = some b) : b.index j = a.index j := by
  cases op <;> simp only [leavesIndex] at hs <;> simp only [execInstr] at he
  all_goals try split at he
  all_goals first | contradiction | (cases he; simp [State.putIndex, State.putData, Function.update, hs])

/-- All caller address registers from index 4 on survive the whole range kernel. -/
theorem range_preserves_index {a b : State K} {n : ℕ}
    (hr : runExactly logRangeProgram a n = some b) {j : ℕ} (hj : 4 ≤ j) :
    b.index j = a.index j := by
  have hcode (op) (hmem : op ∈ logRangeProgram) : leavesIndex j op := by
    simp [logRangeProgram] at hmem
    rcases hmem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst op <;>
      simp [leavesIndex] <;> omega
  have hstep {s t : State K} (h : step logRangeProgram s = some t) :
      t.index j = s.index j := by
    cases ho : s.output with
    | some tag => simp [step,ho] at h
    | none =>
      cases hi : logRangeProgram[s.pc]? with
      | none => simp [step,ho,hi] at h
      | some op =>
        exact keep_index (hcode op (List.mem_of_getElem? hi)) (by simpa [step,ho,hi] using h)
  induction n generalizing b with
  | zero =>
    change some a = some b at hr
    cases hr
    rfl
  | succ n ih =>
    change (runExactly logRangeProgram a n).bind (step logRangeProgram) = some b at hr
    cases hu : runExactly logRangeProgram a n with
    | none => simp [hu] at hr
    | some u =>
      exact (hstep (by simpa [hu] using hr)).trans (ih hu)

end Compression
end LinearProgramming
end Optimization
end OAI

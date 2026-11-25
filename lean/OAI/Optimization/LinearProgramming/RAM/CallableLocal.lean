import OAI.Optimization.LinearProgramming.RAM.Footprint

/-! Finite initialization of an address register representation whose ideal zero has a
nonzero encoding. A bounded RAM execution cannot observe the truncated address tail. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

variable {K : Type*}

/-- Clear address registers above `cap`, leaving the whole scalar bank and control unchanged. -/
def trimIndex (cap : ℕ) (s : State K) : State K :=
  { s with index := fun j => if j≤cap then s.index j else 0 }

@[simp] theorem trimIndex_data (cap : ℕ) (s : State K) : (trimIndex cap s).data=s.data := rfl
@[simp] theorem trimIndex_output (cap : ℕ) (s : State K) : (trimIndex cap s).output=s.output := rfl
@[simp] theorem trimIndex_pc (cap : ℕ) (s : State K) : (trimIndex cap s).pc=s.pc := rfl
@[simp] theorem trimIndex_read {cap j : ℕ} (s : State K) (h : j≤cap) :
    (trimIndex cap s).index j=s.index j := by simp [trimIndex,h]

private theorem trimIndex_setData (cap : ℕ) (s : State K) (d : ℕ) (x : K) :
    trimIndex cap (s.putData d x)=(trimIndex cap s).putData d x := rfl

private theorem trimIndex_setIndex {cap d : ℕ} (s : State K) (x : ℕ) (hd : d≤cap) :
    trimIndex cap (s.putIndex d x)=(trimIndex cap s).putIndex d x := by
  unfold trimIndex State.putIndex
  congr 1
  funext j
  by_cases hj : j=d
  · subst j; simp [hd]
  · simp [Function.update_of_ne hj]

private theorem trimIndex_setPC (cap : ℕ) (s : State K) (pc : ℕ) :
    trimIndex cap {s with pc := pc} = {trimIndex cap s with pc := pc} := rfl

private theorem trimIndex_setOutput (cap : ℕ) (s : State K) (tag : ℕ) :
    trimIndex cap {s with output := some tag} = {trimIndex cap s with output := some tag} := rfl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem exec_trimIndex {i : Instr} {cap : ℕ} (s : State K)
    (hi : i.addressBudget ≤ cap) (ha : ∀ j, s.index j ≤ cap) :
    execInstr i (trimIndex cap s) = (execInstr i s).map (trimIndex cap) := by
  cases i <;> simp only [Instr.addressBudget] at hi
  all_goals
    simp (disch := first | apply ha | omega) only [execInstr,trimIndex_data,trimIndex_read,
      trimIndex_setData,trimIndex_setIndex,trimIndex_setPC,trimIndex_setOutput,Option.map_some,
      apply_ite (Option.map (trimIndex cap)),Option.map_none] <;> rfl

theorem exec_indexBound {s t : State K} {i : Instr} {b : ℕ}
    (hi : i.addressBudget≤b) (hs : ∀j, s.index j≤b) (ht : execInstr i s=some t) :
    ∀j, t.index j≤b+1 := by
  have before : ∀ j, s.index j≤b+1 := fun j => Nat.le_succ_of_le (hs j)
  have write (d v : ℕ) (hv : v≤b+1) : ∀ j, (s.putIndex d v).index j≤b+1 := by
    intro j
    by_cases hd : j=d
    · subst j; simpa [State.putIndex] using hv
    · simpa [State.putIndex,Function.update_of_ne hd] using before j
  cases i with
  | addrConst d v =>
    simp only [execInstr,Option.some.injEq] at ht
    subst t
    exact write d v (by simp only [Instr.addressBudget] at hi; omega)
  | incr d j =>
    simp only [execInstr,Option.some.injEq] at ht
    subst t
    exact write d _ (Nat.succ_le_succ (hs j))
  | decr d j =>
    simp only [execInstr,Option.some.injEq] at ht
    subst t
    exact write d _ ((Nat.sub_le _ _).trans (before j))
  | addrCopy d a | addrLoad d a | addrStore d a =>
    simp only [execInstr,Option.some.injEq] at ht
    subst t
    exact write _ _ (before _)
  | div d a c =>
    by_cases h : s.data c=0
    · simp [execInstr,h] at ht
    · simp [execInstr,h] at ht
      subst t
      exact before
  | const d q | copy d q | add d q _ | sub d q _ | mul d q _ | load d q | store d q =>
    simp only [execInstr,Option.some.injEq] at ht
    subst t
    exact before
  | branchLT d q _ _ | branchAddrLT d q _ _ | jump d | halt d =>
    simp only [execInstr,Option.some.injEq] at ht
    subst t
    exact before

private theorem instruction_le {p : Program} {pc : ℕ} {i : Instr} (h : p[pc]?=some i) :
    i.addressBudget ≤ addressBudget p :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨i,List.mem_of_getElem? h,rfl⟩)

private theorem step_indexBound {p : Program} {s t : State K} {b : ℕ}
    (hp : addressBudget p≤b) (hs : ∀j, s.index j≤b) (ht : step p s=some t) :
    ∀ j, t.index j≤b+1 := by
  cases ho : s.output with
  | some tag => simp [step,ho] at ht
  | none =>
    cases hi : p[s.pc]? with
    | none => simp [step,ho,hi] at ht
    | some i => exact exec_indexBound ((instruction_le hi).trans hp) hs (by simpa [step,ho,hi] using ht)

private theorem step_trimIndex {p : Program} {cap : ℕ} (s : State K)
    (hp : addressBudget p≤cap) (ha : ∀j, s.index j≤cap) :
    step p (trimIndex cap s) = (step p s).map (trimIndex cap) := by
  cases ho : s.output with
  | some tag => simp [step,ho]
  | none =>
    cases hi : p[s.pc]? with
    | none => simp [step,ho,hi]
    | some i => simpa only [step,trimIndex_output,trimIndex_pc,ho,hi] using
        exec_trimIndex s ((instruction_le hi).trans hp) ha

/-- Address values grow by at most one per instruction, including on states with an
ideal nonzero address tail. This statement imposes no finite-support condition. -/
theorem trace_indexBound {p : Program} {s : State K} {b k : ℕ} {tr : Fin (k+1) → State K}
    (hp : addressBudget p≤b) (hs : ∀j, s.index j≤b) (h : Trace p s k tr) (i : Fin (k+1)) :
    ∀ j, (tr i).index j ≤ b+i.val := by
  induction i using Fin.induction with
  | zero => simpa only [Fin.val_zero,Nat.add_zero,h.1] using hs
  | succ j ih => exact step_indexBound (hp.trans (Nat.le_add_right _ _)) ih (h.2 j)

/-- The finite initial prefix yields the same outputs, scalar registers and instruction
count at every instant of the actual native trace. -/
theorem trace_trimIndex {p : Program} {s : State K} {b cap k : ℕ} {tr : Fin (k+1) → State K}
    (hp : addressBudget p≤b) (hs : ∀j, s.index j≤b) (h : Trace p s k tr) (hc : b+k≤cap) :
    Trace p (trimIndex cap s) k (fun i => trimIndex cap (tr i)) := by
  refine ⟨congrArg _ h.1,?_⟩
  intro i
  have hsize : b+i.castSucc.val≤cap := by have := i.isLt; simp only [Fin.val_castSucc]; omega
  have ha := trace_indexBound hp hs h i.castSucc
  rw [step_trimIndex _ (by omega : addressBudget p≤cap) (fun j => (ha j).trans hsize),h.2 i]
  rfl

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

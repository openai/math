import OAI.Optimization.LinearProgramming.RAM.CallableLocalRun

/-! A bounded RAM call can run in a finite window of a larger heap and preserve the
surrounding heap literally. Both scalar and address registers outside the window are live. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

variable {K : Type*}

def windowMemory (cap : ℕ) (tail live : Memory K) : Memory K where
  data j := if j≤cap then live.data j else tail.data j
  index j := if j≤cap then live.index j else tail.index j

def windowState (cap : ℕ) (tail : Memory K) (s : State K) : State K :=
  let m := windowMemory cap tail s.memory
  {s with data := m.data, index := m.index}

private theorem data_read {cap j : ℕ} (tail : Memory K) (s : State K) (hj : j≤cap) :
    (windowState cap tail s).data j=s.data j := by simp [windowState,windowMemory,State.memory,hj]

private theorem index_read {cap j : ℕ} (tail : Memory K) (s : State K) (hj : j≤cap) :
    (windowState cap tail s).index j=s.index j := by simp [windowState,windowMemory,State.memory,hj]

private theorem writeWindow {α : Type*} {cap d : ℕ} (outside inside : ℕ → α) (value : α) (hd : d≤cap) :
    (fun j => if j≤cap then Function.update inside d value j else outside j) =
      Function.update (fun j => if j≤cap then inside j else outside j) d value := by
  funext j
  by_cases hit : j=d
  · subst j; simp [hd]
  · simp [Function.update_of_ne hit]

private theorem state_writeData {cap d : ℕ} (tail : Memory K) (s : State K) (x : K) (hd : d≤cap) :
    windowState cap tail (s.putData d x)=(windowState cap tail s).putData d x :=
  congrArg (fun bank => State.mk (s.pc+1) bank (windowState cap tail s).index s.output)
    (writeWindow tail.data s.data x hd)

private theorem state_writeIndex {cap d : ℕ} (tail : Memory K) (s : State K) (v : ℕ) (hd : d≤cap) :
    windowState cap tail (s.putIndex d v)=(windowState cap tail s).putIndex d v :=
  congrArg (fun bank => State.mk (s.pc+1) (windowState cap tail s).data bank s.output)
    (writeWindow tail.index s.index v hd)

private theorem state_setPC (cap : ℕ) (tail : Memory K) (s : State K) (pc : ℕ) :
    windowState cap tail {s with pc := pc} = {windowState cap tail s with pc := pc} := rfl

private theorem state_setOutput (cap : ℕ) (tail : Memory K) (s : State K) (v : ℕ) :
    windowState cap tail {s with output := some v} = {windowState cap tail s with output := some v} := rfl

@[simp] theorem windowState_pc (cap : ℕ) (tail : Memory K) (s : State K) :
    (windowState cap tail s).pc=s.pc := rfl
@[simp] theorem windowState_output (cap : ℕ) (tail : Memory K) (s : State K) :
    (windowState cap tail s).output=s.output := rfl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem exec_windowState {i : Instr} {cap : ℕ} (tail : Memory K) (s : State K)
    (hi : i.addressBudget≤cap) (ha : ∀ j,s.index j≤cap) :
    execInstr i (windowState cap tail s)=(execInstr i s).map (windowState cap tail) := by
  cases i <;> simp only [Instr.addressBudget] at hi
  all_goals
    simp (disch := first | apply ha | omega) only [execInstr,data_read,index_read,state_writeData,
      state_writeIndex,state_setPC,state_setOutput,Option.map_some,
      apply_ite (Option.map (windowState cap tail)),Option.map_none]

private theorem step_windowState {p : Program} {cap : ℕ} (tail : Memory K) (s : State K)
    (hp : addressBudget p≤cap) (ha : ∀j,s.index j≤cap) :
    step p (windowState cap tail s)=(step p s).map (windowState cap tail) := by
  cases ho : s.output with
  | some v => simp [step,ho]
  | none =>
    cases hi : p[s.pc]? with
    | none => simp [step,ho,hi]
    | some ins =>
      have him : ins.addressBudget∈p.map Instr.addressBudget := List.mem_map.mpr
        ⟨ins,List.mem_of_getElem? hi,rfl⟩
      have hle : ins.addressBudget≤addressBudget p := List.le_sum_of_mem him
      simpa only [step,windowState_pc,windowState_output,ho,hi] using exec_windowState tail s (hle.trans hp) ha

/-- Even an unbounded external memory can be used as the background for the full trace. -/
theorem trace_windowState {p : Program} {s : State K} {b cap k : ℕ} {tr : Fin (k+1) → State K}
    (tail : Memory K) (hp : addressBudget p≤b) (hs : ∀j,s.index j≤b) (h : Trace p s k tr)
    (hc : b+k≤cap) : Trace p (windowState cap tail s) k (fun i => windowState cap tail (tr i)) := by
  refine ⟨congrArg _ h.1,?_⟩
  intro i
  have hsize : b+i.castSucc.val≤cap := by have := i.isLt; simp only [Fin.val_castSucc]; omega
  have ha := trace_indexBound hp hs h i.castSucc
  rw [step_windowState tail _ (by omega : addressBudget p≤cap) (fun j => (ha j).trans hsize),h.2 i]
  rfl

/-- Execute a relocated fragment in a larger sparse heap. No assumption on the external
address values is needed. Only the untouched exterior scalars must satisfy `P`. -/
theorem Fragment.run_at_window {f : Fragment} {P : K → Prop} {m t : Memory K} {bound cap b : ℕ}
    (run : f.Run P m bound t) (prog : Program) (pc : ℕ) (code : CodeAt prog pc (f.emit pc))
    (tail : Memory K) (hP : ∀j,cap<j → P (tail.data j))
    (hp : addressBudget prog≤b) (hi : ∀j,m.index j≤b) (hc : b+bound≤cap) :
    ∃ k≤bound, Execution prog (fun s => ∀j,P (s.data j))
      ((windowMemory cap tail m).atPC pc) k ((windowMemory cap tail t).atPC (pc+f.size)) := by
  obtain ⟨k,hk,work⟩ := run prog pc code
  obtain ⟨tr,ht,he,hs⟩ := work.to_trace
  have real := trace_windowState tail hp hi ht ((Nat.add_le_add_left hk b).trans hc)
  have safe (i : Fin (k+1)) (j : ℕ) : P ((windowState cap tail (tr i)).data j) := by
    change P (if j≤cap then (tr i).data j else tail.data j)
    split_ifs with h
    · exact hs i j
    · exact hP j (by omega)
  have out := Execution.of_trace (safe := fun st => ∀j,P (st.data j)) real safe
  change Execution prog _ _ k (windowState cap tail (tr (Fin.last k))) at out
  rw [he] at out
  exact ⟨k,hk,out⟩

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

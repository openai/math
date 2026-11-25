import OAI.Optimization.LinearProgramming.RAM.CallableLocalFrame
import OAI.Optimization.LinearProgramming.RAM.CallableScopedClamp

/-! Index growth and memory-window simulation at the accessed instruction. Scalar operations
reuse the original step proof. Branches read only their two compared registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem access_indexBound {s t : State K} {i : Instr} {b : ℕ} (hi : i.accessBudget≤b)
    (hs : ∀ j, s.index j≤b) (run : execInstr i s=some t) : ∀ j,t.index j≤b+1 := by
  by_cases full : i.addressBudget≤b
  · exact exec_indexBound (i:=i) full hs run
  cases i <;> try exact (full hi).elim
  all_goals
    simp only [execInstr,Option.some.injEq] at run
    subst t
    exact fun j => Nat.le_succ_of_le (hs j)

/-- Index values along the actual trace grow at most one per instruction, irrespective
of all absolute jump targets in the surrounding code. -/
theorem trace_access_indexBound {p : Program} {s : State K} {k b : ℕ} {tr : Fin (k+1)→State K}
    (hb : ∀ i∈p,i.accessBudget≤b) (hs : ∀ j,s.index j≤b) (h : Trace p s k tr) (i : Fin (k+1)) :
    ∀ j,(tr i).index j≤b+i.val := by
  induction i using Fin.induction with
  | zero => simpa only [Fin.val_zero,Nat.add_zero,h.1] using hs
  | succ i ih =>
    have edge := h.2 i
    cases ho : (tr i.castSucc).output with
    | some tag => simp [step,ho] at edge
    | none =>
      cases hf : p[(tr i.castSucc).pc]? with
      | none => simp [step,ho,hf] at edge
      | some op =>
        have hop := (hb op (List.mem_of_getElem? hf)).trans (Nat.le_add_right b i.val)
        exact access_indexBound hop ih (by simpa [step,ho,hf] using edge)

private theorem trim_access {i : Instr} {cap : ℕ} (s : State K) (hi : i.accessBudget≤cap)
    (ha : ∀ j,s.index j≤cap) : execInstr i (trimIndex cap s) = (execInstr i s).map (trimIndex cap) := by
  cases i <;> try exact exec_trimIndex s hi ha
  all_goals try rfl
  case branchAddrLT a b y n =>
    change a+b≤cap at hi
    exact congrArg (fun pc => some {trimIndex cap s with pc := pc})
      (congrArg₂ (fun u v : ℕ => if u<v then y else n)
        (trimIndex_read s (by omega : a≤cap)) (trimIndex_read s (by omega : b≤cap)))

private theorem win_access {i : Instr} {cap : ℕ} (tail : Memory K) (s : State K) (hi : i.accessBudget≤cap)
    (ha : ∀ j,s.index j≤cap) : execInstr i (windowState cap tail s)=(execInstr i s).map (windowState cap tail) := by
  cases i <;> try exact exec_windowState tail s hi ha
  all_goals try rfl
  case branchLT a b y n =>
    change a+b≤cap at hi
    have rd (j : ℕ) (hj : j≤cap) : (windowState cap tail s).data j=s.data j := by
      simp [windowState,windowMemory,State.memory,hj]
    exact congrArg (fun pc => some {windowState cap tail s with pc := pc})
      (congrArg₂ (fun u v : K => if u<v then y else n) (rd a (by omega)) (rd b (by omega)))
  case branchAddrLT a b y n =>
    change a+b≤cap at hi
    have rd (j : ℕ) (hj : j≤cap) : (windowState cap tail s).index j=s.index j := by
      simp [windowState,windowMemory,State.memory,hj]
    exact congrArg (fun pc => some {windowState cap tail s with pc := pc})
      (congrArg₂ (fun u v : ℕ => if u<v then y else n) (rd a (by omega)) (rd b (by omega)))

private theorem map_trace {p : Program} {s : State K} {k b cap : ℕ} {tr : Fin (k+1)→State K}
    (f : State K→State K) (pc : ∀ s,(f s).pc=s.pc) (out : ∀ s,(f s).output=s.output)
    (simulate : ∀ (i : Instr) (x : State K), i.accessBudget≤cap → (∀ j,x.index j≤cap) →
      execInstr i (f x) = (execInstr i x).map f)
    (budget : ∀ i∈p,i.accessBudget≤b) (start : ∀ j,s.index j≤b) (run : Trace p s k tr)
    (room : b+k≤cap) : Trace p (f s) k (fun i => f (tr i)) := by
  refine ⟨congrArg f run.1,?_⟩
  intro i
  have step₀ := run.2 i
  let x := tr i.castSucc
  have grow := trace_access_indexBound budget start run i.castSucc
  have size : b+i.castSucc.val≤cap := by
    have := i.isLt
    simp only [Fin.val_castSucc]
    omega
  have hindex : ∀ j,x.index j≤cap := fun j => (grow j).trans size
  change step p (f x) = some (f (tr i.succ))
  change step p x = some (tr i.succ) at step₀
  cases ho : x.output with
  | some tag => simp [step,ho] at step₀
  | none =>
    cases hf : p[x.pc]? with
    | none => simp [step,ho,hf] at step₀
    | some op =>
      have hop : op.accessBudget≤cap := (budget op (List.mem_of_getElem? hf)).trans (by omega)
      simp only [step,out,pc,ho,hf]
      have executed : execInstr op x=some (tr i.succ) := by simpa [step,ho,hf] using step₀
      exact (simulate op x hop hindex).trans (congrArg (Option.map f) executed)

theorem trace_trim_access {p : Program} {s : State K} {k b cap : ℕ} {tr : Fin (k+1)→State K}
    (budget : ∀ i∈p,i.accessBudget≤b) (start : ∀ j,s.index j≤b) (run : Trace p s k tr) (room : b+k≤cap) :
    Trace p (trimIndex cap s) k (fun i => trimIndex cap (tr i)) :=
  map_trace (trimIndex cap) (trimIndex_pc cap) (trimIndex_output cap) (fun _ x => trim_access x)
    budget start run room

theorem trace_window_access {p : Program} {s : State K} {k b cap : ℕ} {tr : Fin (k+1)→State K}
    (tail : Memory K) (budget : ∀ i∈p,i.accessBudget≤b) (start : ∀ j,s.index j≤b) (run : Trace p s k tr)
    (room : b+k≤cap) : Trace p (windowState cap tail s) k (fun i => windowState cap tail (tr i)) :=
  map_trace (windowState cap tail) (windowState_pc cap tail) (windowState_output cap tail)
    (fun _ x => win_access tail x) budget start run room

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

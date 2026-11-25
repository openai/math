import OAI.Optimization.LinearProgramming.PrimalDual.SubroutineCalls
import OAI.Optimization.LinearProgramming.PrimalDual.CallSegmentsCore

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace SubroutineCalls

open RAM RAM.Block CallSegments

theorem stateAt_fin {k : ℕ} (tr : Fin (k+1) → State ℚ) (i : Fin (k+1)) : stateAt tr i.val = tr i :=
  congrArg tr (Fin.ext (Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)))

theorem trace_stepAt {p : Program} {s : State ℚ} {k : ℕ} {tr : Fin (k+1) → State ℚ}
    (run : Trace p s k tr) {i : ℕ} (hi : i < k) : step p (stateAt tr i) = some (stateAt tr (i+1)) := by
  let j : Fin k := ⟨i,hi⟩
  have l : stateAt tr i = tr j.castSucc := stateAt_fin tr j.castSucc
  have r : stateAt tr (i+1) = tr j.succ := stateAt_fin tr j.succ
  rw [l,r]; exact run.2 j

theorem window_run {p : Program} {s : State ℚ} {k : ℕ} {tr : Fin (k+1) → State ℚ}
    (run : Trace p s k tr) {off n : ℕ} (fit : off+n ≤ k) :
    Trace p (stateAt tr off) n (window tr off n) := by
  refine ⟨by simp [window],?_⟩
  intro j
  change step p (stateAt tr (off+j.val)) = some (stateAt tr (off+(j.val+1)))
  simpa only [Nat.add_assoc] using trace_stepAt run (i:=off+j.val) (by have := j.isLt; omega)

theorem slice_agrees {p : Program} {s x : State ℚ} {k off n : ℕ} {tr : Fin (k+1) → State ℚ}
    (full : Trace p s k tr) (startEq : x = stateAt tr off) (fit : off+n ≤ k) {u : Fin (n+1) → State ℚ}
    (part : Trace p x n u) : u = window tr off n := by
  rw [startEq] at part
  exact CallSegments.unique_trace part (window_run full fit)

theorem end_after {p : Program} {safe : State ℚ → Prop} {s x y : State ℚ} {k off n : ℕ}
    {tr : Fin (k+1) → State ℚ} (full : Trace p s k tr) (startEq : x = stateAt tr off) (fit : off+n ≤ k)
    (part : Execution p safe x n y) : y = stateAt tr (off+n) := by
  obtain ⟨u,localRun,last,_⟩ := part.to_trace
  exact last.symm.trans (congrFun (slice_agrees full startEq fit localRun) (Fin.last n))

theorem block_range_on {host : Program} {H pc off n k : ℕ} {b : Block} {u v : Memory ℚ} {s : State ℚ}
    {tr : Fin (k+1) → State ℚ} (full : Trace host s k tr) (startEq : u.atPC pc = stateAt tr off)
    (fit : off+n ≤ k) (placed : CodeAt host pc (b.compile pc)) (work : Block.Eval (Within H) b u n v) :
    ∀ i : Fin n, pc ≤ (window tr off n i.castSucc).pc ∧ (window tr off n i.castSucc).pc < pc+b.size := by
  obtain ⟨raw,r,_,range⟩ := fixedBlock_confined placed work
  have equal := slice_agrees full startEq fit r
  exact equal ▸ range

theorem terminal_range_on {host : Program} {H pc off n k tag : ℕ} {b : Block} {u v : Memory ℚ} {s : State ℚ}
    {tr : Fin (k+1) → State ℚ} (full : Trace host s k tr) (startEq : u.atPC pc = stateAt tr off)
    (fit : off+(n+1) ≤ k) (placed : CodeAt host pc (b.compile pc++[.halt tag]))
    (work : Block.Eval (Within H) b u n v) : ∀ i : Fin (n+1),
    pc ≤ (window tr off (n+1) i.castSucc).pc ∧ (window tr off (n+1) i.castSucc).pc < pc+b.size+1 := by
  have room : off+n ≤ k := by omega
  intro i
  change pc ≤ (stateAt tr (off+i.val)).pc ∧ (stateAt tr (off+i.val)).pc < pc+b.size+1
  by_cases hi : i.val < n
  · let j : Fin n := ⟨i.val,hi⟩
    have r := block_range_on full startEq room placed.left work j
    change pc ≤ (stateAt tr (off+i.val)).pc ∧ (stateAt tr (off+i.val)).pc < pc+b.size at r
    exact ⟨r.1,by omega⟩
  · have eq : i.val = n := by have := i.isLt; omega
    have last := end_after full startEq room (work.compile_correct placed.left)
    rw [eq,← last]
    change pc ≤ pc+b.size ∧ pc+b.size < pc+b.size+1
    omega

theorem embedded_on {host guest : Program} {site : Site} {H U off n k tag : ℕ} {dims : List ℕ} {input : List ℚ}
    {valid : State ℚ → Prop} {before after : Memory ℚ} {s : State ℚ} {tr : Fin (k+1) → State ℚ}
    (full : Trace host s k tr) (startEq : before.atPC site.entry = stateAt tr off) (fit : off+n ≤ k) (wide : H ≤ U) (separate : site.ret tag ≠ site.entry)
    (work : Embedded host guest H site.entry site.ret dims input valid tag before after n) :
    GuestOn host guest site U dims input valid tag tr off n := by
  have last := end_after full startEq fit work.physical
  obtain ⟨raw,r,_,range⟩ := work.confined
  have equal := slice_agrees full startEq fit r
  have positive : 0 < n := by
    by_contra h
    have same : off+n = off := by omega
    apply separate
    calc site.ret tag = (stateAt tr (off+n)).pc := congrArg State.pc last
         _ = (stateAt tr off).pc := by rw [same]
         _ = site.entry := (congrArg State.pc startEq).symm
  refine ⟨fit,positive,window_run full fit,(congrArg State.pc startEq).symm,(congrArg State.output startEq).symm,
    (congrArg State.pc last).symm,(congrArg State.output last).symm,?_,?_,?_,?_⟩
  · exact equal ▸ range
  · rw [← startEq]; exact work.inputData
  · rw [← startEq]; exact work.inputIndex
  · obtain ⟨l,u,re,good,tagged,clock,bits,back⟩ := work.virtual
    refine ⟨l,u,re,good,tagged,clock,fun i j => (bits i j).trans wide,?_⟩
    rw [← last,← startEq]
    exact ⟨back.data,back.index,back.callerData,back.callerIndex⟩

end SubroutineCalls
end PrimalDual
end LinearProgramming
end Optimization
end OAI

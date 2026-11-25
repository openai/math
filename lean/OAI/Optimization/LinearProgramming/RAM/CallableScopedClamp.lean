import OAI.Optimization.LinearProgramming.RAM.CallableScopedAccess

/-! Restrict the ambient ROM's memory operands while proving a local call, then replay its
successful execution in the original ROM, at the same absolute program counter. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

def clampInstr (cap : ℕ) (i : Instr) : Instr := if i.accessBudget≤cap then i else .halt 0

def clampProgram (cap : ℕ) (p : Program) : Program := p.map (clampInstr cap)

theorem clampProgram_budget (p : Program) (cap : ℕ) {i : Instr} (hi : i ∈ clampProgram cap p) : i.accessBudget≤cap := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  by_cases hj : j.accessBudget≤cap
  · rw [clampInstr,ite_eq_left hj]; exact hj
  · rw [clampInstr,ite_eq_right hj]; exact Nat.zero_le cap

theorem clampProgram_code {f : Fragment} {p : Program} {pc cap : ℕ}
    (bound : f.Scoped cap) (h : CodeAt p pc (f.emit pc)) : CodeAt (clampProgram cap p) pc (f.emit pc) := by
  have eqn : (f.emit pc).map (clampInstr cap) = f.emit pc := by
    calc
      _ = (f.emit pc).map id := List.map_congr_left fun i hi => by simp [clampInstr,bound pc i hi]
      _ = _ := List.map_id _
  obtain ⟨pre,post,hlen,rfl⟩ := h
  exact ⟨pre.map (clampInstr cap),post.map (clampInstr cap),by simpa using hlen,
    by simp only [clampProgram,List.map_append,eqn]⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem earlier_live {p : Program} {safe : State K→Prop} {s t : State K} {k : ℕ}
    (h : Execution p safe s k t) (last : t.output=none) : s.output=none := by
  cases h with
  | done => exact last
  | next _ hs _ =>
    cases ho : s.output with
    | none => rfl
    | some tag => simp [step,ho] at hs

private theorem replay_step {p : Program} {cap : ℕ} {s t : State K}
    (hs : step (clampProgram cap p) s=some t) (live : t.output=none) : step p s=some t := by
  cases ho : s.output with
  | some k => simp [step,ho] at hs
  | none =>
    cases hi : p[s.pc]? with
    | none => simp [step,ho,clampProgram,hi] at hs
    | some op =>
      by_cases hb : op.accessBudget≤cap
      · simpa [step,ho,clampProgram,hi,clampInstr,hb] using hs
      · simp [step,ho,clampProgram,hi,clampInstr,hb,execInstr] at hs
        subst t
        contradiction

/-- A clamped instruction that was replaced by `halt` is excluded by the live endpoint.
This also covers fragments that branch to another part of the ambient ROM. -/
theorem replay_clamped {p : Program} {cap : ℕ} {safe : State K→Prop} {s t : State K} {k : ℕ}
    (h : Execution (clampProgram cap p) safe s k t) (last : t.output=none) : Execution p safe s k t := by
  induction h with
  | done x hx => exact .done x hx
  | next hx step rest ih => exact .next hx (replay_step step (earlier_live rest last)) (ih last)

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

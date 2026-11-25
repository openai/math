import OAI.Optimization.LinearProgramming.Games.RAMLayout

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Games
namespace OrbitRAM

open RAM

private def noDataWrite (j : ℕ) : Instr → Prop
  | .const d _ | .copy d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .div d _ _ | .load d _ => j ≠ d
  | .store .. => False
  | _ => True

def noIndexWrite (j : ℕ) : Instr → Prop
  | .addrConst d _ | .addrCopy d _ | .incr d _ | .decr d _ | .addrLoad d _ => j ≠ d
  | .addrStore .. => False
  | _ => True

private theorem data_unchanged {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (j : ℕ) {i : Instr} (h : noDataWrite j i) {s t : State K} (step : execInstr i s = some t) :
    t.data j = s.data j := by
  cases i <;> simp only [noDataWrite,execInstr] at h step
  all_goals try (split at step <;> try contradiction)
  all_goals (cases step; simp_all [State.putData, State.putIndex])

theorem index_unchanged {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (j : ℕ) {i : Instr} (h : noIndexWrite j i) {s t : State K} (step : execInstr i s = some t) :
    t.index j = s.index j := by
  cases i <;> simp only [noIndexWrite,execInstr] at h step
  all_goals try (split at step <;> try contradiction)
  all_goals (cases step; simp_all [State.putData, State.putIndex])

def onlyOps (R : Instr → Prop) : Block → Prop
  | .skip => True
  | .op i => R i
  | .seq a b | .branch _ a b => onlyOps R a ∧ onlyOps R b
  | .loop _ b => onlyOps R b

theorem block_frame {K T : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {safe : Memory K → Prop} {b : Block} {m t : Memory K} {k : ℕ} (h : Block.Eval safe b m k t)
    (R : Instr → Prop) (F : Memory K → T)
    (preserves : ∀ {i s u}, R i → (∀ pc, execInstr i (Memory.atPC s pc) = some (Memory.atPC u (pc+1))) → F u = F s)
    (restrict : onlyOps R b) : F t = F m := by
  induction h with
  | skip => rfl
  | op _ _ step => exact preserves restrict step
  | seq _ _ ih₁ ih₂ => exact (ih₂ restrict.2).trans (ih₁ restrict.1)
  | branchTrue _ _ ih => exact ih restrict.1
  | branchFalse _ _ ih => exact ih restrict.2
  | loopFalse => rfl
  | loopTrue _ _ _ ih₁ ih₂ => exact (ih₂ restrict).trans (ih₁ restrict)

/-- The table and all scalar slots outside 0–3 are preserved. Address register
1 retains the vertex count; address registers 6 onward are available to the caller. -/
theorem evaluator_frame {m t : Memory ℚ} {k : ℕ} {safe : Memory ℚ → Prop}
    (h : Block.Eval safe evaluator m k t) :
    (∀ j, 4 ≤ j → t.data j = m.data j) ∧
    ∀ j, j = 1 ∨ 6 ≤ j → t.index j = m.index j := by
  constructor
  · intro j hj
    apply block_frame h (noDataWrite j) (fun μ ↦ μ.data j)
      (fun hi ex ↦ data_unchanged j hi (ex 0))
    simp [evaluator,burn,init,cycleLoop,cycleStep,setFlag,Block.forRange,Block.straight,onlyOps,noDataWrite]; omega
  · intro j hj
    apply block_frame h (noIndexWrite j) (fun μ ↦ μ.index j)
      (fun hi ex ↦ index_unchanged j hi (ex 0))
    simp [evaluator,burn,init,cycleLoop,cycleStep,setFlag,Block.forRange,Block.straight,onlyOps,noIndexWrite]; omega

end OrbitRAM
end Games
end LinearProgramming
end Optimization
end OAI

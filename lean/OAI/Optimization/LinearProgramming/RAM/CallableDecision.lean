import OAI.Optimization.LinearProgramming.RAM.CallableBase

/-! A data-dependent final decision for a complete RAM caller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Fragment

/-- A fixed physical program that ends with a conditional return tag. -/
def decisionProgram (f : Fragment) (c : Cond) (yes no : ℕ) : Program :=
  f.emit 0 ++ [c.instr (f.size+1) (f.size+2), .halt yes, .halt no]

theorem run_decision {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f : Fragment} {P : K → Prop} {m t : Memory K} {bound : ℕ} (run : f.Run P m bound t)
    (c : Cond) (yes no : ℕ) :
    ∃ l≤bound+2, ∃ tr : Fin (l+1) → State K,
      Trace (decisionProgram f c yes no) (m.atPC 0) l tr ∧
      (tr (Fin.last l)).output=some (if c.test t then yes else no) ∧
      (tr (Fin.last l)).memory=t ∧ ∀ i j,P ((tr i).data j) := by
  let prog := decisionProgram f c yes no
  have whole : CodeAt prog 0 (f.emit 0 ++ [c.instr (f.size+1) (f.size+2),.halt yes,.halt no]) := CodeAt.whole _
  obtain ⟨k,hk,part⟩ := run prog 0 whole.left
  simp only [Nat.zero_add] at part
  have tail := whole.right
  rw [f.length_emit,Nat.zero_add] at tail
  have test := Block.Eval.test_exec (safe := fun z : Memory K => ∀j,P (z.data j)) prog c t f.size
    (f.size+1) (f.size+2) part.safe_end tail.head
  let endPC := if c.test t then f.size+1 else f.size+2
  let tag := if c.test t then yes else no
  have fetch : prog[endPC]?=some (.halt tag) := by
    cases h : c.test t with
    | false => simpa [endPC,tag,h] using (Block.Eval.tail_at (Block.Eval.tail_at tail)).head
    | true => simpa [endPC,tag,h] using (Block.Eval.tail_at tail).head
  let last : State K := {t.atPC endPC with output := some tag}
  have halt : Execution prog (fun s => ∀ j,P (s.data j)) (t.atPC endPC) 1 last :=
    .one part.safe_end (by simp [step,Memory.atPC,fetch,execInstr,last]) part.safe_end
  obtain ⟨tr,ht,he,hs⟩ := ((part.append test).append halt).to_trace
  exact ⟨k+1+1,(by omega),tr,ht,he ▸ rfl,he ▸ rfl,hs⟩

end Fragment
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

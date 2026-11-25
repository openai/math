import OAI.Optimization.LinearProgramming.RAM.CallableOddMemory

/-! Simulation of a complete structured caller over the odd address and scalar registers.
The unmodified even-register callee can be linked to native service blocks. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

/-- Recursively lift the operations and guards of a structured program to the odd bank. -/
def block : RAM.Block → RAM.Block
  | .skip => .skip
  | .op i => instr i
  | .seq a b => .seq (block a) (block b)
  | .branch c a b => .branch (cond c) (block a) (block b)
  | .loop c b => .loop (cond c) (block b)

/-- Every operation, test and back edge of the ordinary RAM simulation is charged. The
same fixed callee memory appears at both ends, and the scalar predicate holds throughout. -/
theorem block_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (callee : RAM.Memory K) (hc : callee.AllData P)
    {b : RAM.Block} {m t : RAM.Memory K} {k : ℕ} (h : RAM.Block.Eval (RAM.Memory.AllData P) b m k t) :
    ∃ l ≤ 4*k, RAM.Block.Eval (RAM.Memory.AllData P) (block b) (memory callee m) l (memory callee t) := by
  induction h with
  | @skip m hs => exact ⟨0, by omega, .skip (allData callee m hc hs)⟩
  | @op i m t hs ht hi =>
    exact ⟨instrCost i, by simpa using instrCost_le i, instr_eval P callee hc i (.op hs ht hi)⟩
  | seq _ _ ia ib =>
    obtain ⟨ka,ha,ea⟩ := ia
    obtain ⟨kb,hb,eb⟩ := ib
    exact ⟨ka+kb,by omega,ea.seq eb⟩
  | @branchTrue c a b m t k test _ ih =>
    obtain ⟨l,hl,ev⟩ := ih
    exact ⟨1+l+1,by omega,.branchTrue (by rw [cond_test]; exact test) ev⟩
  | @branchFalse c a b m t k test _ ih =>
    obtain ⟨l,hl,ev⟩ := ih
    exact ⟨1+l,by omega,.branchFalse (by rw [cond_test]; exact test) ev⟩
  | @loopFalse c b m test hs =>
    exact ⟨1,by omega,.loopFalse (by rw [cond_test]; exact test) (allData callee m hc hs)⟩
  | @loopTrue c b m n t k l test _ _ ihb ihr =>
    obtain ⟨kb,hb,eb⟩ := ihb
    obtain ⟨kr,hr,er⟩ := ihr
    exact ⟨1+kb+1+kr,by omega,.loopTrue (by rw [cond_test]; exact test) eb er⟩

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

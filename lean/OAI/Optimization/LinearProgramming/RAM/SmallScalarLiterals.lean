import OAI.Optimization.LinearProgramming.RAM.Code

/-! Scalar literals in compiled RAM blocks. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Block

/-- Every scalar literal in a structured program is zero or one. Fixed register addresses
and natural control indices are kept separate from scalar inputs in the RAM. -/
def SmallScalarLiterals : Block → Prop
  | .skip => True
  | .op (.const _ q) => q = 0 ∨ q = 1
  | .op _ => True
  | .seq a b | .branch _ a b => a.SmallScalarLiterals ∧ b.SmallScalarLiterals
  | .loop _ a => a.SmallScalarLiterals

private theorem const_ne_branch (dst : ℕ) (q : ℚ) (c : Cond) (yes no : ℕ) :
    Instr.const dst q ≠ c.instr yes no := by cases c <;> simp [Cond.instr]

/-- Structured assembly preserves the scalar-literal restriction in the executable instruction list. -/
theorem SmallScalarLiterals.compile (b : Block) (h : b.SmallScalarLiterals) (pc dst : ℕ) (q : ℚ)
    (hi : Instr.const dst q ∈ b.compile pc) : q=0 ∨ q=1 := by
  induction b generalizing pc with
  | skip => simp [Block.compile] at hi
  | op i =>
    have he : Instr.const dst q = i := by simpa [Block.compile] using hi
    subst i
    exact h
  | seq a b ia ib =>
    rcases List.mem_append.mp hi with ha | hb
    · exact ia h.1 _ ha
    · exact ib h.2 _ hb
  | branch c a b ia ib =>
    simp [Block.compile,const_ne_branch] at hi
    rcases hi with ha | hb
    · exact ia h.1 _ ha
    · exact ib h.2 _ hb
  | loop c a ia =>
    simp [Block.compile,const_ne_branch] at hi
    exact ia h _ hi

end Block
end RAM
end LinearProgramming
end Optimization
end OAI

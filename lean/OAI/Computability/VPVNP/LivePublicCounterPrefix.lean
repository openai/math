import OAI.Computability.VPVNP.LivePublicCounter

/-!
# Loading the two auxiliary operands read from the processor's own prefix

The live program has no copy of its own text in its instruction table. Its
fixed expression vector computes the length-only operands and leaves zeros
in the two prefix slots. It copies the prefix length and packed prefix from
the parsed input into those two slots.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CounterPublic

open BurstRAM BurstRAM.PrivateRAM PrimedCounter

/-- The finite expression vector whose instruction table is independent of the actual prefix. -/
def shape (c : Constants) (j : Fin 34) : PublicExpr :=
  if j.val = 7 ∨ j.val = 12 then .lit 0 else table UniversalMachine.emptyProgram c j

theorem table_other (c : Constants) (p : UniversalMachine.Program) (j : Fin 34)
    (h7 : j.val ≠ 7) (h12 : j.val ≠ 12) : shape c j = table p c j := by
  simp only [shape, h7, h12, or_self, ↓reduceIte]
  revert h7 h12
  refine Fin.addCases (m := 16) (n := 18) (fun j ↦ ?_) (fun j ↦ ?_) j
  · intro h7 h12
    simp only [table,ParserPublic.Inputs.table, Fin.append_left, ParserPublic.paperInputs]
    fin_cases j
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (h7 rfl).elim
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (h12 rfl).elim
    · rfl
    · rfl
    · rfl
  · intro _ _
    simp only [table,ParserPublic.Inputs.table, Fin.append_right]
    rfl

end LiveProgram.CounterPublic

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.RAMProgram

namespace OAI
/-! # The bounded-cost deterministic instruction fragment for tagged control -/

namespace Hierarchy.TaggedShorterCheapCPU
open Computability.VPVNP.BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- Opcodes with ripple addition, word comparison, or direct data transfer.
All external reads and writes are certified by the common memory trace. -/
def Cheap : Instr w p r k → Prop
  | .constant .. | .publicWord .. | .stateWord .. | .copy .. => True
  | .binary .add .. | .binary .sub .. | .binary .bitAnd .. => True
  | .jumpEq .. | .jumpLt .. | .readExternal .. | .writeExternal .. => True
  | .returnState .. | .accept | .reject => True
  | _ => False

theorem deterministic (M : Machine w p r k) (all : ∀ i, Cheap (M.code i))
    (c : Config w p r) (f : Bool → Config w p r) : M.program.step c ≠ .branch f := by
  have good := all c.pc
  change (M.code c.pc).run M.publicData c ≠ _
  generalize eqn : M.code c.pc = a at good ⊢
  cases a <;> simp_all [Cheap,Instr.run]

end Hierarchy.TaggedShorterCheapCPU

end OAI

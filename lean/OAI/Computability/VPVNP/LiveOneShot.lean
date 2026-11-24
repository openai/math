import OAI.Computability.VPVNP.RAMUniform

/-!
# Closing a single-call stage of the live program

The descriptor initializer ends by returning a word. At its stage boundary
this is a normal accepting exit that lets the linker select the next stage.
The instruction trace, bit consumption, memory probes, and required fuel
agree with the original call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveOneShot

open BurstRAM BurstRAM.PrivateRAM

variable {p r k w : ℕ}

private def closeInstruction : Instr w p r k → Instr w p r k
  | .returnState _ => .accept
  | i => i

/-- Close the returning exits of a single-call native template so the enclosing linker can
advance after its first call. -/
def oneShot (T : Template p r k) : Template p r k :=
  { T with code := fun pc => closeInstruction (T.code pc) }

private def closeAction {C : Type*} : CallAction w C → CallAction w C
  | .finish _ => .finish none
  | action => action

private theorem step_eq (T : Template p r k) (pub : Fin k → Word w) (c : Config w p r) :
    ((oneShot T).instantiate w pub).program.step c =
      closeAction ((T.instantiate w pub).program.step c) := by
  simp only [oneShot, Template.instantiate, Machine.program]
  cases T.code c.pc <;> rfl

/-- Executing the closed table changes every successful return to acceptance. -/
theorem execute_oneShot (T : Template p r k) (pub : Fin k → Word w) (fuel : ℕ)
    (c : Config w p r) (m : Memory w) (bs : List Bool) :
    execute ((oneShot T).instantiate w pub).program fuel c m bs =
      (execute (T.instantiate w pub).program fuel c m bs).map (fun t => ⟨t.events, none⟩) := by
  induction fuel generalizing c m bs with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute, step_eq]
    cases (T.instantiate w pub).program.step c with
    | finish v => cases bs <;> rfl
    | reject => rfl
    | branch f => cases bs <;> simp [closeAction, ih, Option.map_map, Function.comp_def, Report.prepend]
    | localStep next | read a next | write a v next =>
      simp [closeAction, ih, Option.map_map, Function.comp_def, Report.prepend]

end LiveOneShot

end VPVNP
end Computability
end OAI

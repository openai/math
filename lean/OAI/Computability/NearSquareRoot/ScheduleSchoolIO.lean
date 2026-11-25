import OAI.Computability.IntegerMultiplication.Interface
import Batteries.Tactic.OpenPrivate

/-!
# Delimited input and fixed-width output for the schoolbook candidate

The commands operate on register zero. A Boolean pair enters in raw tape order
with a single separator. The length of each input is preserved by encoding, so
the same command handles every leading-zero pattern.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schoolbook
open IntegerMultiplication IntegerMultiplication.Code

/-- A raw stream on register zero and empty stacks on every other register. -/
def raw (s : List Ltr) : Reg Ltr := fun i => if i = 0 then s else []

@[simp] theorem raw_zero (s : List Ltr) : raw s 0 = s := rfl

theorem letters_pile_empty (t : Tree) :
    letters (pile 0 t (fun _ => [])) = raw t.spell := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [letters, raw]
  · simp [letters, raw, hi]

open private go outList unload from OAI.Computability.IntegerMultiplication.Interface

/-- P192's fixed program that encodes the delimited MSF pair as a tree. -/
def loadCmd : Cmd := go

/-- P192's fixed program that removes list constructors from the MSF output. -/
def unloadCmd : Cmd := .tie outList

theorem load_run (x y : List Bool) (env : Env) :
    Prog.Run env loadCmd (raw (x.map Ltr.bit ++ .sep :: y.map Ltr.bit))
      (17 + 11 * (x.length + y.length)) (raw (send (x, y)).spell) :=
  Interface.load x y env

theorem unload_run (z : List Bool) (env : Env) :
    Prog.Run env unloadCmd (raw (send z).spell)
      (6 + 12 * z.length) (raw (z.map Ltr.bit)) := by
  rw [show 6 + 12 * z.length = 1 + (5 + 12 * z.length) by omega]
  exact Prog.Run.tie (unload z env)

end Schoolbook

end NearSquareRoot
end Computability
end OAI

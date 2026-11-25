import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # The seven setup instructions of a physical bit-array checker -/

namespace ThreeFlat.RAM.TickCheckSetup

open Computability.VPVNP.BurstRAM PrivateRAM
variable {w p r k : ℕ}

def values (start old new finish : Word w) : Fin 7 → Word w :=
  ![start,0,old,new,1,4,finish]

def emit (P : Fin 7 → Fin p) (R : Fin 7 → Fin r)
    (V : Fin 7 → Word w) (exit : Fin p) : Fin 7 → Instr w p r k
  | 0 => .constant (R 0) (V 0) (P 1)
  | 1 => .constant (R 1) (V 1) (P 2)
  | 2 => .constant (R 2) (V 2) (P 3)
  | 3 => .constant (R 3) (V 3) (P 4)
  | 4 => .constant (R 4) (V 4) (P 5)
  | 5 => .constant (R 5) (V 5) (P 6)
  | _ => .constant (R 6) (V 6) exit

def loaded (P : Fin 7 → Fin p) (R : Fin 7 → Fin r) (V : Fin 7 → Word w)
    (exit : Fin p) (c : Config w p r) :=
  let d := ((c.put (P 1) (R 0) (V 0)).put (P 2) (R 1) (V 1)).put (P 3) (R 2) (V 2)
  let f := ((d.put (P 4) (R 3) (V 3)).put (P 5) (R 4) (V 4)).put (P 6) (R 5) (V 5)
  f.put exit (R 6) (V 6)

@[simp] theorem loaded_reg (P : Fin 7 → Fin p) (R : Fin 7 ↪ Fin r) (V : Fin 7 → Word w)
    (exit : Fin p) (c : Config w p r) (j : Fin 7) : (loaded P R V exit c).reg (R j) = V j := by
  fin_cases j <;> simp [loaded,Config.put,Function.update,R.injective.eq_iff]

theorem advance_setup (M : Machine w p r k) (P : Fin 7 → Fin p) (R : Fin 7 ↪ Fin r)
    (V : Fin 7 → Word w) (exit : Fin p) (rom : ∀ i, M.code (P i) = emit P R V exit i)
    (c : Config w p r) (m : Memory w) (entry : c.pc = P 0) :
    advance M.program 7 c m = some (loaded P R V exit c,m) := by
  simp [advance,Machine.program,entry,rom,emit,Instr.run,loaded,Config.put]

end ThreeFlat.RAM.TickCheckSetup

end OAI

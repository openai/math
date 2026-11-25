import OAI.ThreeFlat.RAM.ContinuationLink
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Instructions for the chronological reverse parent scan -/
namespace ThreeFlat.RAM.HistoryNodeDirectory.Reverse
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Fin.CommRing
variable {w p r k : ℕ}

/-- From arbitrary registers, load the compact root directory pointer,
S6+1 (number of terminal roots), and the private root-index scratch base. -/
def code (P : Fin 23 → Fin p) (R : Fin 9 → Fin r) (params : Fin 3 → Fin k) (exit : Fin p) (pc : Fin 23) : Instr w p r k :=
  match pc.val with
  | 0 => .publicWord (R 7) (params 0) (P 1)
  | 1 => .readExternal (R 6) (R 7) (P 2)
  | 2 => .constant (R 2) 1 (P 3)
  | 3 => .binary .add (R 7) (R 7) (R 2) (P 4)
  | 4 => .readExternal (R 4) (R 7) (P 5)
  | 5 => .publicWord (R 7) (params 1) (P 6)
  | 6 => .readExternal (R 0) (R 7) (P 7)
  | 7 => .binary .add (R 0) (R 0) (R 6) (P 8)
  | 8 => .publicWord (R 5) (params 2) (P 9)
  | 9 => .constant (R 1) 0 (P 10)
  | 10 => .constant (R 3) 8 (P 11)
  | 11 => .jumpEq (R 0) (R 1) exit (P 12)
  | 12 => .binary .sub (R 0) (R 0) (R 2) (P 13)
  | 13 => .jumpLt (R 0) (R 6) (P 14) (P 22)
  | 14 => .binary .mul (R 7) (R 0) (R 3) (P 15)
  | 15 => .binary .add (R 7) (R 7) (R 4) (P 16)
  | 16 => .binary .add (R 7) (R 7) (R 2) (P 17)
  | 17 => .readExternal (R 7) (R 7) (P 18)
  | 18 => .binary .add (R 7) (R 7) (R 5) (P 19)
  | 19 => .readExternal (R 8) (R 7) (P 20)
  | 20 => .binary .add (R 7) (R 5) (R 0) (P 21)
  | 21 => .writeExternal (R 7) (R 8) (P 11)
  | _ => .binary .sub (R 8) (R 0) (R 6) (P 20)

def block (w : ℕ) : Block w 23 9 3 where
  first := 0
  emit pc reg data exit := code pc reg data exit

end ThreeFlat.RAM.HistoryNodeDirectory.Reverse

end OAI

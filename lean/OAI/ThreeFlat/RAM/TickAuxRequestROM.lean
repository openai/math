import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.TickGuardRule

namespace OAI
/-! # Generating and executing auxiliary comparison records from the runtime header -/

namespace ThreeFlat.RAM.TickAuxRequestGen

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickChronology Diagonal.TickAuxiliary
open scoped Fin.CommRing

variable {w k : ℕ}

/-- The four runtime control words are phase, branch, persistent-field end,
and active pair-field end. Their addresses are fixed for the entire machine. -/
def row (addr : Fin 4 → Word w) : Term w k 1 :=
  (TickGuardRule.program w k).instantiate ![(Term.literal (addr 0)).load,(Term.literal (addr 1)).load,
    .result 0,(Term.literal (addr 2)).load,(Term.literal (addr 3)).load]

def header {a : ℕ} (A : Layout a) (p : Phase) (run : Bool) : Fin 4 → Word w :=
  ![(p.tag : Word w),(run.toNat : Word w),(A.wiresEnd : Word w),(A.pairsEnd : Word w)]

theorem row_binds (addr : Fin 4 → Word w) : (row (k:=k) addr).binds ≤ 88 := by
  have h := TickGuardRule.program_binds w k
  simp [row,Term.load,Term.literal,Term.binds,Fin.sum_univ_succ]
  omega

end ThreeFlat.RAM.TickAuxRequestGen

end OAI

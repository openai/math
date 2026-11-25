import OAI.Optimization.LinearProgramming.Compression.InnerControl
import OAI.Optimization.LinearProgramming.Compression.InnerSessionTransport

/-! The outer continuation stores one short mode tag followed by its public inputs or
committed rationals and the subroutine continuation. No stage duplicates its prior trace. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

theorem epochCarry_size (x : Input) (w : Word) (k : Driver.Carry) :
    (WordDialogue.stateCode inputEncoding carryCode (.inr (w,.inl (x,k)))).length ≤
      (WordDialogue.stateCode Driver.inputCode Driver.carryCode (.inr (w,k))).length + 2*(inputCode x).length+4 := by
  simp [WordDialogue.stateCode,carryCode,epochCarryCode,sumCode,prodCode,pairBits_length]
  omega

theorem requestCarry_size (c : RequestContext) (w : Word) (k : Driver.Carry) :
    (WordDialogue.stateCode inputEncoding carryCode (.inr (w,.inr (.inl (c,k))))).length ≤
      (WordDialogue.stateCode Driver.inputCode Driver.carryCode (.inr (w,k))).length + 2*(requestContextCode c).length+4 := by
  simp [WordDialogue.stateCode,carryCode,requestCarryCode,sumCode,prodCode,pairBits_length]
  omega

theorem graphCarry_size (gamma : Rats) (w : Word) (k : Graph.Carry) :
    (WordDialogue.stateCode inputEncoding carryCode (.inr (w,.inr (.inr (gamma,k))))).length ≤
      (WordDialogue.stateCode RequestTable.inputCode RequestTable.Dialogue.carryCode (.inr (w,k))).length + 2*(Projector.rowCode gamma).length+4 := by
  simp [WordDialogue.stateCode,carryCode,graphCarryCode,sumCode,prodCode,pairBits_length]
  omega

def sessionSize (x : Input) (gamma : Rats) (le lr lg : ℕ) (answer : Option ℚ) :=
  12+le+lr+lg+(inputEncoding x).length+2*(inputCode x).length+
    2*(requestContextCode (x,gamma)).length+2*(Projector.rowCode gamma).length+(outputWord answer).length

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI

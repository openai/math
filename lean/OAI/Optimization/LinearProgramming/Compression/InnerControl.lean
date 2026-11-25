import OAI.Optimization.LinearProgramming.Compression.InnerRoundRows
import OAI.Optimization.LinearProgramming.Lattice.BitRoundingKernels
import OAI.Optimization.LinearProgramming.Compression.InnerGraph
import OAI.Optimization.LinearProgramming.Compression.RoundingBudgets

/-! Finite-state sequencing of the two native sign-rounding dialogues and the graph/grid
dialogue. All external requests use the same signed list of generator and candidate exponents. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner

open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

abbrev RequestContext := Input × Rats
abbrev EpochCarry := Input × Driver.Carry
abbrev RequestCarry := RequestContext × Driver.Carry
abbrev GraphCarry := Rats × Graph.Carry
abbrev Carry := EpochCarry ⊕ (RequestCarry ⊕ GraphCarry)
abbrev Action := Word ⊕ (Word × Carry)

def requestContextCode := prodCode inputCode Projector.rowCode
def epochCarryCode := prodCode inputCode Driver.carryCode
def requestCarryCode := prodCode requestContextCode Driver.carryCode
def graphCarryCode := prodCode Projector.rowCode RequestTable.Dialogue.carryCode
def carryCode := sumCode epochCarryCode (sumCode requestCarryCode graphCarryCode)
def actionCode := sumCode (id : Word → Word) (prodCode (id : Word → Word) carryCode)

def epochInput (x : Input) : Driver.Input :=
  (x.1.2+1,epochFormBudget x.1.2 (paperWidth x.1.1) (epochHeightFor x.1.1 x.1.2))

def requestInput (x : Input) : Driver.Input :=
  (x.1.2+2,(x.1.2+3)*(requestCutoff (x.1.2+1)+3))

def routeGraph (gamma : Rats) : Graph.Action → Action
  | .inl v => .inl (outputWord (affineResult gamma v))
  | .inr (w,c) => .inr (w,.inr (.inr (gamma,c)))

noncomputable def routeRequest (c : RequestContext) : Round.Action → Action
  | .inl z => routeGraph c.2 (Graph.dispatch (.inl (paperGrid c.1.1.1,normalizeRow z)))
  | .inr (a,k) => .inr (Driver.signPacket a,.inr (.inl (c,k)))

noncomputable def routeEpoch (x : Input) : Round.Action → Action
  | .inl z =>
    let gamma := normalizeRow z
    if x.2.1 then .inl (outputWord (some (readAt 0 gamma x.2.2)))
    else routeRequest (x,gamma) (Round.dispatch Driver.actualKernels (.inl (requestInput x)))
  | .inr (a,k) => .inr (Driver.signPacket (padRow a),.inl (x,k))

noncomputable def dispatch : Input ⊕ (Word × Carry) → Action
  | .inl x => routeEpoch x (Round.dispatch Driver.actualKernels (.inl (epochInput x)))
  | .inr (w,.inl (x,k)) => routeEpoch x (Round.dispatch Driver.actualKernels (.inr (w,k)))
  | .inr (w,.inr (.inl (c,k))) => routeRequest c (Round.dispatch Driver.actualKernels (.inr (w,k)))
  | .inr (w,.inr (.inr (gamma,k))) => routeGraph gamma (Graph.dispatch (.inr (w,k)))

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI

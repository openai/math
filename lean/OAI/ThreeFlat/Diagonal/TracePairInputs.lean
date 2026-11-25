import OAI.ThreeFlat.Diagonal.TraceIssueCore
import OAI.ThreeFlat.Diagonal.TraceWordOrder
import OAI.ThreeFlat.Diagonal.TraceBoolNet
import OAI.ThreeFlat.Diagonal.TraceBinaryOps
import OAI.ThreeFlat.Diagonal.TraceFormulaPacket
import OAI.ThreeFlat.Diagonal.TraceRowCode

namespace OAI
/-! # The bit circuits feeding a fetched RAM instruction from two packed rows -/

namespace ThreeFlat.Diagonal.TracePair

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM TraceBanks TraceRows TraceWords TraceIssue
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

/-- False addresses the current row and true addresses its successor. -/
abbrev Raw (w r : ℕ) := Bool × Fin (5+r) × Fin (w+1)

def headerWire (side : Bool) (i : Fin 5) (j : Fin (w+1)) : Expr (Raw w r) :=
  .input (side, i.castAdd r, j)

def registerWire (side : Bool) (i : Fin r) (j : Fin w) : Expr (Raw w r) :=
  .input (side, Fin.natAdd 5 i, j.castSucc)

def wordIs (side : Bool) (i : Fin 5) (v : Word (w+1)) : Expr (Raw w r) :=
  sameWord (headerWire side i) (fun j => .const (bits v j))

def tagNumber : Tag → Fin 8
  | .tick => 1 | .left => 2 | .right => 3 | .read => 4 | .write => 5 | .accept => 6 | .result => 7

def tagIs (side : Bool) (t : Fin 8) : Expr (Raw w r) :=
  wordIs side 0 (Fin.ofNat _ t.val)

def pcIs (side : Bool) (i : Fin p) : Expr (Raw w r) :=
  wordIs side 1 (Fin.ofNat _ i.val)

def terminal : Expr (Raw w r) := (tagIs false 6).or (tagIs false 7)

def next (e : Bool → Expr (Raw w r)) : Expr (Raw w r) := Expr.mux terminal (e false) (e true)

/-- Both arithmetic inputs are addressed directly at the current register file. -/
def operandInput (a b : Fin r) : Fin (w+w) → Raw w r ⊕ Bool :=
  Fin.addCases (fun j => Sum.inl (false, Fin.natAdd 5 a, j.castSucc))
    (fun j => Sum.inl (false, Fin.natAdd 5 b, j.castSucc))

def cmpExpr : Instr w p r k → Expr (Raw w r)
  | .jumpEq a b .. => sameWord (registerWire false a) (registerWire false b)
  | .jumpLt a b .. => lessWord (registerWire false a) (registerWire false b)
  | _ => .const false

noncomputable def aluPacket (pub : Fin k → Word w) (j : Fin w) : Instr w p r k → TraceCompose.Packet (Raw w r)
  | .constant _ v _ => formulaPacket (.const (bits v j))
  | .publicWord _ i _ => formulaPacket (.const (bits (pub i) j))
  | .binary op _ a b _ =>
    ⟨_, TraceBoolNet.outputCircuit (operandInput a b) (TraceBinaryOps.network op w) j⟩
  | _ => formulaPacket (.const false)

/-- One circuit for each local input, including the selected operation result
and the two comparison instructions. The two Bool ports detect padding. -/
noncomputable def packet (M : Machine w p r k) : Port w p r ⊕ Bool → TraceCompose.Packet (Raw w r)
  | .inr side => formulaPacket (tagIs side 0)
  | .inl (.tag t) => formulaPacket (tagIs false (tagNumber t))
  | .inl (.reg a j) => formulaPacket (registerWire false a j)
  | .inl (.nextReg a j) => formulaPacket (next (fun side => registerWire side a j))
  | .inl (.state j) => formulaPacket (headerWire false 2 j.castSucc)
  | .inl (.nextState j) => formulaPacket (next (fun side => headerWire side 2 j.castSucc))
  | .inl (.pc i) => formulaPacket (pcIs false i)
  | .inl (.nextPC i) => formulaPacket (next (fun side => pcIs side i))
  | .inl (.address j) => formulaPacket (headerWire false 3 j)
  | .inl (.data j) => formulaPacket (headerWire false 4 j)
  | .inl (.alu i j) => aluPacket M.publicData j (M.code i)
  | .inl (.cmp i) => formulaPacket (cmpExpr (M.code i))

/-- On a padding row, only another padding row may follow. On an active row,
the right-hand padding flag agrees with the current instruction's halt flag. -/
def checkExpr (M : Machine w p r k) : Expr (Port w p r ⊕ Bool) :=
  let halt := (Expr.input (.inl (.tag .accept))).or (.input (.inl (.tag .result)))
  let pad0 := Expr.input (.inr false)
  let pad1 := Expr.input (.inr true)
  Expr.mux pad0 pad1 ((same halt pad1).and ((issue M).rename Sum.inl))

noncomputable def pairCircuit (M : Machine w p r k) : TraceCompose.Packet (Raw w r) :=
  TraceCompose.substituteFintype (packet M) (formulaPacket (checkExpr M)).2

theorem pairCircuit_eval (M : Machine w p r k) (x : Raw w r → Bool) :
    (pairCircuit M).2.eval x = (checkExpr M).eval (fun a => ((packet M a).2.eval x)) := by
  rw [pairCircuit, TraceCompose.substituteFintype_eval, formulaPacket_eval]

end ThreeFlat.Diagonal.TracePair

end OAI

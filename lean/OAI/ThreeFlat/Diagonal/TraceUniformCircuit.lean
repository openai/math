import OAI.ThreeFlat.Diagonal.TraceProgramCandidate
import OAI.ThreeFlat.Diagonal.TraceProgramDispatch

namespace OAI
/-! # Uniform native instruction dispatch from the physical program text -/

namespace ThreeFlat.Diagonal.TraceProgram

open RAM TraceWords TraceIssue TracePair TraceDecodeShape
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

noncomputable instance shapeFintype : Fintype (Instr 0 p r k) :=
  Fintype.ofList (InstructionShapes.all p r k) InstructionShapes.mem_all

abbrev Control (w p r k : ℕ) := Input w p r k ⊕ (Fin p × Instr 0 p r k)

noncomputable def source : Control w p r k → TraceCompose.Packet (Input w p r k)
  | .inl a => pin a
  | .inr (i,z) => candidateCircuit i z

def rowControl (e : Expr (Raw w r)) : Expr (Control w p r k) :=
  e.rename fun a => Sum.inl (Sum.inl a)

def fields (i : Fin p) (f : Fin 6) (j : Fin w) : Expr (Control w p r k) :=
  .input (.inl (.inr (instructionField i f,j)))

noncomputable def slot (i : Fin p) : Expr (Control w p r k) :=
  selectSlot (fields i) (fun z => .input (.inr (i,z)))

noncomputable def control : Expr (Control w p r k) :=
  Expr.mux (rowControl (tagIs false 0)) (rowControl (tagIs true 0))
    (TraceFetch.fetch (fun i => rowControl (pcIs false i)) slot)

noncomputable def uniformPair : TraceCompose.Packet (Input w p r k) :=
  TraceCompose.substituteFintype source (formulaPacket (control (w:=w) (p:=p) (r:=r) (k:=k))).2

end ThreeFlat.Diagonal.TraceProgram

end OAI

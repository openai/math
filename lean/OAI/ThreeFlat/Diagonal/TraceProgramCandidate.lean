import OAI.ThreeFlat.Diagonal.TracePairInputs
import OAI.ThreeFlat.Diagonal.TraceProgramText
import OAI.ThreeFlat.Diagonal.TraceDecodeShape

namespace OAI
/-! # A two-row circuit for one shape with operands supplied in program text -/

namespace ThreeFlat.Diagonal.TraceProgram

open RAM TraceWords TraceIssue TracePair TraceDecodeShape
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

/-- Local input contains the two packed rows and the shared program text. -/
abbrev Input (w p r k : ℕ) := Raw w r ⊕ Text w p k

def pin {σ : Type*} (a : σ) : TraceCompose.Packet σ :=
  ⟨0, ⟨.nil, .var a⟩⟩

@[simp] theorem pin_eval {σ : Type*} (a : σ) (x : σ → Bool) : (pin a).2.eval x = x a := rfl

noncomputable def liftPacket (e : TraceCompose.Packet (Raw w r)) : TraceCompose.Packet (Input w p r k) :=
  TraceCompose.substituteFintype (fun a => pin (Sum.inl a)) e.2

@[simp] theorem liftPacket_eval (e : TraceCompose.Packet (Raw w r)) (x : Input w p r k → Bool) :
    (liftPacket e).2.eval x = e.2.eval (fun i => x (.inl i)) := by simp [liftPacket]

@[simp] theorem liftPacket_size (e : TraceCompose.Packet (Raw w r)) :
    (liftPacket (p:=p) (k:=k) e).1 = e.1 := by simp [liftPacket, pin]

def single (i : Fin p) (z : Instr 0 p r k) (v : Word w) (pub : Fin k → Word w) : Machine w p r k :=
  ⟨i,fun _ => instantiate z v,pub⟩

def literalAt (data : Memory w) (i : Fin p) : Word w :=
  data (instructionAddress i.val + 2)

def publicValues (data : Memory w) (c : Fin k) : Word w := data (1+6*p+c.val)

def native (data : Memory w) (i : Fin p) (z : Instr 0 p r k) : Machine w p r k :=
  single i z (literalAt data i) (publicValues (p:=p) data)

/-- Literal and public ROM operands come directly from their program text pins.
All other ALU and comparison packets have shape-fixed wiring. -/
noncomputable def candidatePacket (i : Fin p) (z : Instr 0 p r k) (a : Port w p r ⊕ Bool) :
    TraceCompose.Packet (Input w p r k) :=
  match a, z with
  | .inl (.alu _ j), .constant .. => pin (.inr (instructionField i 2,j))
  | .inl (.alu _ j), .publicWord _ c _ => pin (.inr (publicField c,j))
  | _, _ => liftPacket (packet (single i z 0 (fun _ => 0)) a)

noncomputable def candidateCircuit (i : Fin p) (z : Instr 0 p r k) : TraceCompose.Packet (Input w p r k) :=
  TraceCompose.substituteFintype (candidatePacket i z)
    (formulaPacket (checkExpr (single i z (0 : Word w) (fun _ => 0)))).2

private theorem checkExpr_payload (i : Fin p) (z : Instr 0 p r k) (v : Word w) (pub : Fin k → Word w) :
    checkExpr (single i z (0 : Word w) (fun _ => 0)) = checkExpr (single i z v pub) := by
  cases z <;> rfl

private theorem candidatePacket_eval (data : Memory w) (x : Raw w r → Bool)
    (i : Fin p) (z : Instr 0 p r k) (a : Port w p r ⊕ Bool) :
    (candidatePacket i z a).2.eval (Sum.elim x (contents data)) = (packet (native data i z) a).2.eval x := by
  cases a with
  | inr side => simp [candidatePacket, packet, native, single]
  | inl a =>
    cases a with
    | alu q j =>
      cases z <;> simp [candidatePacket, packet, aluPacket, native, single, instantiate,
        contents, literalAt, instructionField, publicValues, publicField, Expr.eval]
    | cmp q =>
      cases z <;> simp [candidatePacket, packet, cmpExpr, native, single, instantiate]
    | _ => simp [candidatePacket,packet]

theorem candidateCircuit_eval (data : Memory w) (x : Raw w r → Bool) (i : Fin p) (z : Instr 0 p r k) :
    (candidateCircuit i z).2.eval (Sum.elim x (contents data)) =
      (pairCircuit (native data i z)).2.eval x := by
  simp only [candidateCircuit, TraceCompose.substituteFintype_eval, formulaPacket_eval,
    candidatePacket_eval, pairCircuit_eval, native, checkExpr_payload i z (literalAt data i) (publicValues (p:=p) data)]

end ThreeFlat.Diagonal.TraceProgram

end OAI

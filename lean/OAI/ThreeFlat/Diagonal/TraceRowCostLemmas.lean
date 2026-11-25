import OAI.ThreeFlat.Diagonal.TraceUniformPackets
import OAI.ThreeFlat.Diagonal.TracePacketArray
import OAI.ThreeFlat.Diagonal.TraceCostFormula
import OAI.ThreeFlat.Diagonal.TracePacketCost

namespace OAI
/-! # An absolute polynomial bound for all gates in a physical trace row -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM TraceRows TraceBanks TraceWords TraceRowPackets TraceProgram TraceCompose
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {F : Type*} [CommRing F] [Fintype F] {w p r k d S f : ℕ}

theorem canonical_bound (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) :
    (canonicalFrame (r:=r) hw hp).circuitSize () ≤ canonicalCost w p r := by
  exact (TracePair.formulaPacket_size_le (canonical hw hp)).trans (Nat.mul_le_mul_left 4 (canonical_size hw hp))

theorem terminal_bound (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (i : Option F) :
    (TraceTerminal.rowFrame hF hw r).circuitSize i ≤ terminalCost (Fintype.card F) w := by
  apply ((TraceTerminal.rowFrame hF hw r).circuitSize_le i).trans
  exact Nat.mul_le_mul_left 4 (TraceTerminal.rowFrame_size hF hw r)

theorem first_bound (hp : p ≤ 2^(w+1)) (s : Fin 2) (st : Word w) :
    (TracePair.formulaPacket (startFromText hp (textExpr (p:=p) (k:=k))
        (fun j => .const (bits (wide st) j)) (cpuExpr' (r:=r) (d:=d) s))).1 ≤ firstCost w p r := by
  apply (TracePair.formulaPacket_size_le _).trans
  exact Nat.mul_le_mul_left 4 (startFromText_size hp _ _ _ (fun _ => le_rfl)
    (fun _ => le_rfl) (fun _ => le_rfl))

theorem ordinary_size (q : Packet (LocalPort w r d)) : (ordinary (p:=p) (k:=k) q).1 = q.1 := by
  simp [ordinary,substituteFintype_size,TraceRowPackets.read]

theorem joint_size (s : Fin 2) (j : Input w p r k) :
    (joint (d:=d) s j).1 = 0 := by
  cases j with
  | inl a => obtain ⟨b,j,k⟩ := a; simp [joint,ordinary_size,pairRead,TraceRowPackets.read]
  | inr j => rfl

theorem card_check (F : Type*) [Fintype F] (w p k : ℕ) :
    Fintype.card (Check F w p k) = (1+2*(3+(Fintype.card F+1))) + (1+(1+6*p+k)*w*2) := by
  simp [Check,Factor,Text,Nat.mul_assoc]

end ThreeFlat.Diagonal.TraceUniformRow

end OAI

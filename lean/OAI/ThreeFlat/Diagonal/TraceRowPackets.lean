import OAI.ThreeFlat.Diagonal.TraceMemoryPacketInputs
import OAI.ThreeFlat.Diagonal.TracePhysicalPorts
import OAI.ThreeFlat.Diagonal.TraceInitialCircuit
import OAI.ThreeFlat.Diagonal.TracePairInputs
import OAI.ThreeFlat.Diagonal.TraceTerminal

namespace OAI
/-! # Actual weighted Boolean packets located at one physical trace row -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMSerialization BooleanTranscript VerifierNetwork
open TraceBanks TraceWords TraceSlots TraceRows TraceCompose
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {F : Type*} {w p r k f S d : ℕ}

/-- All row-local factors have public ordinals, two CPU slots and one
sorted-memory validation. -/
abbrev Factor (F : Type*) := Unit ⊕ (Fin 2 × (Fin 3 ⊕ Option F))

def pairRead (s : Fin 2) : TracePair.Raw w r → Packet (LocalPort w r d)
  | (b,j,k) => read (cpuPin (if b then s.succ else s.castSucc) (finProdFinEquiv (j,k)))

/-- Inactive clock positions contribute the scalar one. The last circuit
receives the canonical zero padding word bundle on the successor port. -/
noncomputable def packet [Fintype F] [Zero F] (hF : Fintype.card F ≤ 2^w)
    (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (M : Machine w p r k) (st : Word w)
    (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (v : Fin (2^d)) : Factor F → Packet (LocalPort w r d)
  | .inl _ => memoryPacket hw hs hf v
  | .inr (s,tag) =>
    let a := slotAddress d v s
    let active := decide (S ≤ a ∧ a-S < f)
    match tag with
    | .inl j =>
      match j.val with
      | 0 => if active then substituteFintype (fun jk => read (cpuPin s.castSucc (finProdFinEquiv jk)))
          ((canonicalFrame (r := r) hw hp).circuit ()) else literal true
      | 1 => if active then substituteFintype (pairRead s) (TracePair.pairCircuit M).2 else literal true
      | _ =>
        if a = S ∧ 0 < f then
          TracePair.formulaPacket (initialCheck hp M.entry (fun j => .const (bits (wide st) j)) (cpuExpr s.castSucc))
        else literal (decide (0 < f))
    | .inr i =>
      if active then substituteFintype (fun j => read (cpuPin s.castSucc j))
        ((TraceTerminal.rowFrame hF hw r).circuit i)
      else literal i.isNone

/-- The row scalar is an indicator on validation packets, and the terminal
packet uses the actual finite-field coefficient. -/
def scalar [Zero F] [One F] : Factor F → Bool → F
  | .inl _, b | .inr (_, .inl _), b => if b then 1 else 0
  | .inr (_, .inr i), b => TraceTerminal.unary i b

end ThreeFlat.Diagonal.TraceRowPackets

end OAI

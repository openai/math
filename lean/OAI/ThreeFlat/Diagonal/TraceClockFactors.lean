import OAI.ThreeFlat.Diagonal.TraceCpuPacket

namespace OAI
/-! # Projections for the three CPU validation factors -/

namespace ThreeFlat.Diagonal.TraceRowPackets
open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMSerialization BooleanTranscript
open TraceBanks TraceWords TraceRows TraceCompose

variable {F : Type*} [Fintype F] [Zero F] {w p r k f S d : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (M : Machine w p r k) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) (s : Fin 2)

theorem guardZero :
    packet hF hw hp M st hs hf v (.inr (s,.inl 0)) =
      if decide (S ≤ slotAddress d v s ∧ slotAddress d v s-S<f) then
        substituteFintype (fun jk => read (cpuPin s.castSucc (finProdFinEquiv jk))) ((canonicalFrame (r:=r) hw hp).circuit ())
      else literal true := rfl

theorem guardOne :
    packet hF hw hp M st hs hf v (.inr (s,.inl 1)) =
      if decide (S ≤ slotAddress d v s ∧ slotAddress d v s-S<f) then
        substituteFintype (pairRead s) (TracePair.pairCircuit M).2 else literal true := rfl

theorem guardTwo :
    packet hF hw hp M st hs hf v (.inr (s,.inl 2)) =
      if slotAddress d v s=S ∧ 0<f then
        TracePair.formulaPacket (initialCheck hp M.entry (fun j => .const (bits (wide st) j)) (cpuExpr s.castSucc))
      else literal (decide (0<f)) := rfl

theorem guardTerm (i : Option F) :
    packet hF hw hp M st hs hf v (.inr (s,.inr i)) =
      if decide (S ≤ slotAddress d v s ∧ slotAddress d v s-S<f) then
        substituteFintype (fun j => read (cpuPin s.castSucc j)) ((TraceTerminal.rowFrame hF hw r).circuit i)
      else literal i.isNone := rfl

theorem packetIf_eval {a : Type*} (q : Prop) [Decidable q] (yes no : Packet a) (x : a → Bool) :
    (if q then yes else no).2.eval x=if q then yes.2.eval x else no.2.eval x := by
  by_cases h : q
  · exact (congrArg (fun t : Packet a => t.2.eval x) (ite_eq_left h)).trans (ite_eq_left h).symm
  · exact (congrArg (fun t : Packet a => t.2.eval x) (ite_eq_right h)).trans (ite_eq_right h).symm

end ThreeFlat.Diagonal.TraceRowPackets

end OAI

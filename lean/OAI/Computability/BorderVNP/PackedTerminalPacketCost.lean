import OAI.Computability.BorderVNP.PackedTerminalEmitterCost
import OAI.Computability.BorderVNP.CellPacketGeometryVolume
import OAI.Computability.BorderVNP.PackedTerminalRetainedEmitter

/-! # One Boolean emitter for routing and the ordered sparse cell packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Cover Cover.AddressCircuit Crossing Packing Packing.CellAddressCircuit Packing.RoutingOutputs
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport VPVNP.VerifierNetwork GeometryFrameEncoding
open CellPacketGeometry CellPacketGeometry.LiveWords

variable {I X Y Move EPin IPin Orig HistoryPins : Type} [Fintype HistoryPins] [Fintype I] [Fintype X] [Fintype Y] [Fintype Move]
  [Fintype EPin] [Fintype IPin] {q d V E C PC b w L R n J v reserve s k a : ℕ}
  (enum : Fin q ≃ I) (number : (I → Deck (d+1)) ≃ Fin C) (cf : C ≤ 2^b)
  (p : Params) (vf : V ≤ 2^w) (host width : Fin n → ℕ)
  (name : ℕ → ℕ → ℕ) (hb : b ≤ w) (old : Fin J → Fin V)
  (aux : Frame ((X ⊕ Fin reserve) ⊕ Y) (Fin V × Fin w)) (read : RouteRows.Pins Move q (d+1) V E w → Y)
  (controls : Fin v → Fin (2^w)) (keep : Frame ((X ⊕ Fin reserve) ⊕ Y) HistoryPins)
  (T : Template EPin IPin Orig s PC)
  (up : Frame ((Wires Move q d V E w b ⊕ Bool) ⊕ HistoryPins) (Base s k w EPin IPin))
  (anchors : Frame ((Wires Move q d V E w b ⊕ Bool) ⊕ HistoryPins) (Fin s × Fin a)) (baseOwner : Fin s → Fin PC)
  (pin : Orig → T.Fields) (pad : s < 2^a) (dest H : ℕ)

local notation "rest" => T.orderedFrame up anchors baseOwner pin pad dest H
local notation "packetWords" => Total T.publicDepth T.chunkDepth
local notation "sites" => (p.R+1)*p.sites
local notation "cables" => E+p.slots
local notation "words" => cables*3+(RoutingOutputs.count cables C J sites+((C+(J+C))+(v+packetWords)))
local notation "src" => boundFrame enum number cf (Frame.initial (Sum.inr ∘ read)) aux
local notation "F" => TerminalCells.fields (Move:=Move) (q:=q) (d:=d) (E:=E) vf cf host width
local notation "B" => FieldExport.fields F p name

omit [Fintype I] in
/-- Actual retained-emitter cost for any joint packet program. In particular
the packet may share a single evaluation of its historical and final-row
feeds. Its gate count and output arity appear once each. -/
theorem retainedPacket_bits {o : ℕ} (packet : Frame ((Wires Move q d V E w b ⊕ Bool) ⊕ HistoryPins) (Outputs o w))
    (rows : 1+CellAddressCircuit.count V cables sites C+J+sites ≤ R)
    (key : keyWidth q (d+1) ≤ L) (widths : b ≤ L ∧ w ≤ L ∧ Nat.clog 2 R ≤ L) :
    let output := cables*3+(RoutingOutputs.count cables C J sites+((C+(J+C))+(v+o)))
    let emitted := Retained.emitter B hb old id (Retained.privateControls B old controls packet) (withSewnFields src) keep
    emitted.size+output*w ≤ aux.size+keep.size+packet.size+16000*R*(L+1)^3+4+(3*R+v+o)*w := by
  intro output emitted
  let view := packet.subst (Frame.initial (Sum.elim id (fun _ : HistoryPins => Sum.inr false)))
  let common := terminalEmitter B hb old id (withPrivateViews B old (withControls controls view)) (withSewnFields src)
  have shares : emitted.size = keep.size+common.size := by
    dsimp only [emitted]
    rw [Retained.emitter_size,Retained.privateControls_size]
    simp [common,terminalEmitter,RoutingOutputs.full,withPrivateViews,withControls_size,view]
    omega
  have size : view.size = packet.size := by simp [view]
  have legacy := emitter_cost (Move:=Move) enum number cf p vf host width name hb old aux read controls view rows key widths
  change common.size ≤ aux.size+view.size+16000*R*(L+1)^3+4 at legacy
  have arity : output ≤ 3*R+v+o := by
    simpa only [output,Nat.mul_comm 3 cables] using (output_count (v:=v) (o:=o) rows)
  have wordCost := Nat.mul_le_mul_right w arity
  omega

/-- The genuine pre-lowering Boolean emitter. The real cumulative history pins and the current terminal
field bus are both computed from the same public input. The packet gate DAG is joined to the real routing,
private-view and control words in the same native output table. -/
noncomputable def packetEmitter : Frame ((X ⊕ Fin reserve) ⊕ Y) (Fin words × Fin w) :=
  Retained.emitter B hb old id (Retained.privateControls B old controls rest) (withSewnFields src) keep

local notation "em" => packetEmitter enum number cf p vf host width name hb old aux read controls keep T
  up anchors baseOwner pin pad dest H

omit [Fintype I] in
/-- Gate and output-bit count of the single actual emitter. Its public-volume
term charges the sparse source words before padding and their expression nodes. -/
theorem packetEmitter_size
    (rows : 1+CellAddressCircuit.count V cables sites C+J+sites ≤ R)
    (key : keyWidth q (d+1) ≤ L) (widths : b ≤ L ∧ w ≤ L ∧ Nat.clog 2 R ≤ L)
    (wk : k≤L) (wa : a≤L) (wp : T.publicDepth≤L) (wd : T.chunkDepth≤L)
    (wb : T.recordDepth≤L) (wh : Nat.clog 2 (s+PC) ≤ L) :
    (em).size+words*w ≤ aux.size+keep.size+up.size+anchors.size+
      (20000*R+250050*T.publicVolume+v)*(L+1)^3 := by
  have route := retainedPacket_bits enum number cf p vf host width name hb old aux read controls keep rest rows key widths
  have packet := T.orderedFrame_cubic up anchors baseOwner pin pad dest H L wk widths.2.1 wa wp wd wb wh
  have ones : 1 ≤ (L+1)^3 := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hw : w ≤ (L+1)^3 := widths.2.1.trans (by nlinarith [Nat.zero_le (L^2),Nat.zero_le (L^3)])
  have num : (3*R+v+packetWords)*w ≤ (3*R+v+20*T.publicVolume)*(L+1)^3 :=
    Nat.mul_le_mul (Nat.add_le_add_left T.output_linear _) hw
  change (em).size+words*w ≤ aux.size+keep.size+(rest).size+16000*R*(L+1)^3+4+(3*R+v+packetWords)*w at route
  have add : 4 ≤ 4*R*(L+1)^3 := by
    have hr : 1 ≤ R := by omega
    calc
      4 = 4*1*1 := by decide
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hr) ones
  calc
    _ ≤ aux.size+keep.size+up.size+anchors.size+250000*T.publicVolume*(L+1)^3+
        16000*R*(L+1)^3+4+(3*R+v+20*T.publicVolume)*(L+1)^3 := by omega
    _ ≤ _ := by
      simp only [Nat.add_mul,Nat.mul_assoc] at add ⊢
      omega

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI

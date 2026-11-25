import OAI.Computability.BorderVNP.PackedTerminalPacketCost
import OAI.Computability.BorderVNP.CellPacketGeometryTerminalRate

/-! # Gate and output cost of the physically retained chronological packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Cover Cover.AddressCircuit Crossing Packing Packing.CellAddressCircuit Packing.RoutingOutputs
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport VPVNP.VerifierNetwork GeometryFrameEncoding
open CellPacketGeometry CellPacketGeometry.LiveWords CellPacketGeometry.History CellPacketGeometry.History.Native
open Packing.Inherited.FrozenTape CellSparse.Packet

variable {I X Y Move H Row₀ Payload₀ Row₁ Payload₁ Field Orig : Type} [Fintype I] [Fintype X] [Fintype Y]
  [Fintype Move] [Fintype H] [Fintype Row₀] [Fintype Payload₀] [Fintype Row₁] [Fintype Payload₁] [Fintype Field]
  {q d V E C b w L R n J v reserve a cap k dh dt qa : ℕ}
  (enum : Fin q ≃ I) (number : (I → Deck (d+1)) ≃ Fin C) (cf : C≤2^b)
  (p : Params) (vf : V≤2^w) (host width : Fin n → ℕ) (name : ℕ → ℕ → ℕ)
  (hb : b≤w) (old : Fin J → Fin V) (aux : Frame ((X ⊕ Fin reserve) ⊕ Y) (Fin V × Fin w))
  (read : RouteRows.Pins Move q (d+1) V E w → Y) (controls : Fin v → Fin (2^w))
  (keep : Frame ((X ⊕ Fin reserve) ⊕ Y) H)
  (F : Feeds ((Wires Move q d V E w b ⊕ Bool) ⊕ H) Row₀ Payload₀ Row₁ Payload₁ Field a dh dt k w)
  (S : Schema Row₀ Payload₀) (T : Schema Row₁ Payload₁) (boxes : Fin a → List (Source.Box Orig))
  (sh : ∀ r, (S.tags r).length≤cap) (th : ∀ r, (T.tags r).length≤cap)
  (priv : Fin (C+1) → Field) (rep : Fin (C+1) → List (List Field)) (hd : dh≤qa) (ht : dt≤qa)
  (room : a<2^qa) (croom : C<2^k) (hs : ∀ r, S.width r≤w) (hl : ∀ r, T.width r≤w)
  (base : Fin (roster a S T).length → Fin (C+1)) (pointer : Orig → (template S T boxes sh th priv rep).Fields)
  (pad : (roster a S T).length < 2^qa) (dest header : ℕ)

local notation3 (prettyPrint := false) "template₀" => template S T boxes sh th priv rep
local notation3 (prettyPrint := false) "packet₀" => F.ordered S T boxes sh th priv rep hd ht room croom hs hl base pointer pad dest header
local notation3 "cables" => E+p.slots
local notation3 "sites" => (p.R+1)*p.sites
local notation3 (prettyPrint := false) "src₀" => boundFrame enum number cf (Frame.initial (Sum.inr ∘ read)) aux
local notation3 (prettyPrint := false) "B₀" => FieldExport.fields (TerminalCells.fields (Move:=Move) (q:=q) (d:=d) (E:=E) vf cf host width) p name

omit [Fintype I] in
/-- Count every gate of the returned native terminal frame and every emitted
word bit. The four actual chronological producers, current auxiliary source,
and retained pin frame enter the shared term once. Their packet data include
the entire final binding table and signed report metadata. -/
theorem retainedFeed_bits (rows : 1+CellAddressCircuit.count V cables sites C+J+sites ≤ R)
    (key : keyWidth q (d+1) ≤ L) (widths : b≤L ∧ w≤L ∧ Nat.clog 2 R≤L)
    (wk : k≤L) (wa : qa≤L) (wp : (template₀).publicDepth≤L) (wd : (template₀).chunkDepth≤L)
    (wb : (template₀).recordDepth≤L) (wh : Nat.clog 2 ((roster a S T).length+(C+1))≤L)
    (wl : Nat.clog 2 ((a+1)+(roster a S T).length)≤L) :
    let o := Total (template₀).publicDepth (template₀).chunkDepth
    let out := cables*3+(RoutingOutputs.count cables C J sites+((C+(J+C))+(v+o)))
    let emit := Retained.emitter B₀ hb old id (Retained.privateControls B₀ old controls packet₀) (withSewnFields src₀) keep
    let shared := aux.size+keep.size+F.history.size+F.binding.size+F.table.size+F.field.size
    emit.size+out*w ≤ shared+(20000*R+16008000*sourceVolume S T boxes rep+v)*(L+1)^3 := by
  intro o out emit shared
  have packet := F.ordered_cubic S T boxes sh th priv rep hd ht room croom hs hl base pointer pad dest header L
    wk widths.2.1 wa wp wd wb wh wl
  have full := retainedPacket_bits enum number cf p vf host width name hb old aux read controls keep packet₀ rows key widths
  have count : o≤1280*sourceVolume S T boxes rep := (template₀).output_linear.trans
    ((Nat.mul_le_mul_left 20 (publicVolume_le_source S T boxes sh th priv rep)).trans_eq (by ring))
  have wide : w≤(L+1)^3 := widths.2.1.trans (by nlinarith [Nat.zero_le (L^2),Nat.zero_le (L^3)])
  have bits := Nat.mul_le_mul (Nat.add_le_add_left count (3*R+v)) wide
  have positive : 4≤4*R*(L+1)^3 := by
    have hr : 1≤R := by omega
    have hL : 1≤(L+1)^3 := Nat.succ_le_of_lt (pow_pos (by omega) _)
    exact (by decide : 4≤4*1*1).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hr) hL)
  change emit.size+out*w ≤ aux.size+keep.size+(packet₀).size+16000*R*(L+1)^3+4+(3*R+v+o)*w at full
  change (packet₀).size ≤ F.history.size+F.binding.size+F.table.size+F.field.size+
    16006010*sourceVolume S T boxes rep*(L+1)^3 at packet
  dsimp only [shared]
  simp only [Nat.add_mul,Nat.mul_assoc] at bits positive full packet ⊢
  omega

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI

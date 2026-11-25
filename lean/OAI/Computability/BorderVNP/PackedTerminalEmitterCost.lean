import OAI.Computability.BorderVNP.PackedHistoryRectangleRange
import OAI.Computability.BorderVNP.PackedTerminalRoutingReturn
import OAI.Computability.BorderVNP.PackedTerminalRoutingFields
import OAI.Computability.BorderVNP.PackedRoutingControls

/-! # Cost of the terminal deck and routing emitter

The final catalog lookup uses one sparse table and one query per reserved
site. The same frame then supplies all cable, delivery, address and public
control words. The original history is read once by wire selection.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Cover Cover.AddressCircuit Crossing Packing Packing.CellAddressCircuit Packing.RoutingOutputs
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport VPVNP.VerifierNetwork GeometryFrameEncoding
open private padded lookup_poly from OAI.Computability.BorderVNP.PackedRoutingCost

variable {I X Y Move : Type} [Fintype I] [Fintype X] [Fintype Y] [Fintype Move]
    {q d V E C b w L R n J o v reserve : ℕ} (enum : Fin q ≃ I) (number : (I → Deck (d+1)) ≃ Fin C)
    (cf : C ≤ 2^b)

omit [Fintype I] in
/-- Linear-in-rows cubic-in-word-length cost of the finite cover lookup. -/
theorem owner_cost (rows : C+V ≤ R) (hr : 0<R) (word : keyWidth q (d+1) ≤ L)
    (bits : b ≤ L) (logs : Nat.clog 2 R ≤ L) :
    (frame (V:=V) (E:=E) (w:=w) enum number cf Move).size ≤ 1000*R*(L+1)^3 := by
  have h := frame_size (V:=V) (E:=E) (w:=w) enum number cf Move
  have ord := (Nat.clog_mono_right 2 rows).trans logs
  exact h.trans ((Nat.mul_le_mul (padded rows hr) (lookup_poly word bits ord)).trans (by ring_nf; rfl))

omit [Fintype I] in
/-- Both immutable field bits and all dynamic source arrays contribute their
actual gate counts. The three slot-marker arrays and length-only control
fields are included. All remaining packet outputs contribute through rest. -/
theorem emitter_cost (p : Params) (vf : V ≤ 2^w) (host width : Fin n → ℕ)
    (name : ℕ → ℕ → ℕ) (hb : b ≤ w) (old : Fin J → Fin V)
    (aux : Frame ((X ⊕ Fin reserve) ⊕ Y) (Fin V × Fin w)) (read : RouteRows.Pins Move q (d+1) V E w → Y)
    (controls : Fin v → Fin (2^w)) (rest : Frame (Wires Move q d V E w b ⊕ Bool) (Outputs o w))
    (rows : 1+CellAddressCircuit.count V (E+p.slots) ((p.R+1)*p.sites) C + J + ((p.R+1)*p.sites) ≤ R)
    (word : keyWidth q (d+1) ≤ L) (widths : b ≤ L ∧ w ≤ L ∧ Nat.clog 2 R ≤ L) :
    let src := boundFrame enum number cf (Frame.initial (Sum.inr ∘ read)) aux
    let F := TerminalCells.fields (Move:=Move) (q:=q) (d:=d) (E:=E) vf cf host width
    let B := FieldExport.fields F p name
    let em := terminalEmitter B hb old id (withPrivateViews B old (withControls controls rest)) (withSewnFields src)
    em.size ≤ aux.size + rest.size + 16000*R*(L+1)^3 + 4 := by
  intro src F B em
  have base : 1+(((E+p.slots+C)+(V+C))+(((E+p.slots+(E+p.slots))+(p.R+1)*p.sites)+C))+J+(p.R+1)*p.sites ≤ R := rows
  have lookup := owner_cost (V:=V) (E:=E) (w:=w) (Move:=Move) enum number cf
    (show C+V ≤ R by omega) (by omega) word widths.1 widths.2.2
  have source := boundFrame_size enum number cf
    (Frame.initial (Sum.inr ∘ read) : Frame ((X ⊕ Fin reserve) ⊕ Y) _) aux
  have total := sewn_export_size p F src name hb old (withControls controls rest) rows
    ⟨widths.2.1,widths.1,widths.2.1,widths.2.2⟩
  simp only [Frame.initial_size,Nat.zero_add] at source
  simp only [terminalEmitter,Frame.subst_size,Frame.select_size,em]
  simp only [Frame.subst_size,withControls_size] at total
  change (withSewnFields src).size+(full B hb old id (withPrivateViews B old (withControls controls rest))).size ≤
    src.size+2+rest.size+15000*R*(L+1)^3 at total
  change src.size ≤ aux.size+_+2 at source
  have both : 1000*R*(L+1)^3+15000*R*(L+1)^3 = 16000*R*(L+1)^3 := by ring
  omega

/-- The actual interpreter output-word count includes the cable triples,
placement pairs, private-size views, immutable controls, and remaining
packet words. Its routing contribution is bounded by the same rectangle. -/
theorem output_count {s m n C J A v o R : ℕ}
    (rows : 1+CellAddressCircuit.count s m n C+J+A ≤ R) :
    3*m+(RoutingOutputs.count m C J A+((C+(J+C))+(v+o))) ≤ 3*R+v+o := by
  unfold CellAddressCircuit.count at rows
  unfold RoutingOutputs.count
  omega

/-- The actual quaternion-word key and both pointer widths are polylogarithmic
in the selected team parameters, even when most reserved site rows are vacant. -/
theorem sorting_width (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] {r n R d : ℕ} (hr : 1≤r) (hn : 1≤n)
    (tiles : Fintype.card (I → Deck (d+1)) ≤ R) (space : R ≤ r*n) :
    let H := TeamScales.logWidth r n
    let K := (360*Fintype.card I+60)*H
    keyWidth (Fintype.card I) (d+1) ≤ K ∧ 60*H ≤ K ∧ Nat.clog 2 R ≤ K := by
  classical
  intro H K
  have budget : Nat.clog 2 R ≤ H := by
    change Nat.clog 2 R ≤ TeamScales.logWidth r n
    rw [Shortening.PublicCapacity.public_logWidth]
    exact Nat.clog_mono_right 2 (space.trans (by nlinarith only [Nat.zero_le (r*n)]))
  have hH : 1≤H := by
    change 1 ≤ TeamScales.logWidth r n
    rw [Shortening.PublicCapacity.public_logWidth]
    exact (by decide : 1≤Nat.clog 2 2).trans (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hr hn]))
  have hdepth := Shortening.PublicPopulation.depth_le_clog_tiles I (d+1)
  have hsort := (Nat.clog_mono_right 2 tiles).trans budget
  have hd : d+2 ≤ 4*H := by omega
  have hkey := Nat.mul_le_mul_left (90*Fintype.card I) hd
  have eq : keyWidth (Fintype.card I) (d+1) = 90*Fintype.card I*(d+2) := by
    dsimp [keyWidth,Cover.AddressCircuit.width]; ring
  have base : 60*H ≤ K := Nat.mul_le_mul_right _ (Nat.le_add_left ..)
  have tail : H ≤ 60*H := Nat.le_mul_of_pos_left H (by decide)
  refine ⟨?_,base,budget.trans (tail.trans base)⟩
  rw [eq]
  exact hkey.trans (by dsimp only [K]; rw [Nat.add_mul]; nlinarith only [Nat.zero_le H])

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI

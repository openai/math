import OAI.Computability.BorderVNP.PackedTerminalStagedHistorySource
import OAI.Computability.BorderVNP.PackedTerminalSewnSelectedAux

/-! # The three physical input costs of the staged signed terminal packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Cover Cover.AddressCircuit Crossing Packing Packing.Inherited Packing.SewnField
open Packing.CellAddressCircuit Packing.Inherited.FrozenTape TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open Shortening.PublicCapacity VPVNP.VerifierNetwork PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical
set_option quotPrecheck false
set_option maxHeartbeats 1300000
set_option maxRecDepth 5200

variable {I X Geo Move : Type} [Fintype I] [Fintype X] [Fintype Geo] [Fintype Move]
    {R r t pins link inner n tiles groups copies : ℕ} {Edge : Type}
    (G : Wiring R r t pins link inner n Edge) (htiles : 0 < tiles) (mult : groups*copies=R+1)
    (hg : 0<blockWidth (r*n) tiles) (small : blockWidth (r*n) tiles ≤ link)
    (shape : Shape) {q d C b w J reserve : ℕ} (enum : Fin q ≃ I) (number : (I → Deck (d+1)) ≃ Fin C)
    (cf : C ≤ 2^b) (fmt : Format) (read : RouteRows.Pins Move q (d+1) shape.sites shape.edges w → Geo)
    (vf : shape.sites ≤ 2^w) (host width : Fin (groups*tiles) → ℕ) (mark : ℕ → ℕ → ℕ)

local notation "live" => (R+1)*tiles
local notation "p" => (⟨R,r,G.program.length+t,link,blockWidth (r*n) tiles,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "F" => TerminalCells.fields (Move:=Move) (q:=q) (d:=d) (E:=shape.edges)
  vf cf host width
local notation3 (prettyPrint := false) "B" => FieldExport.fields F p mark
local notation3 (prettyPrint := false) "primary" => frozenPrimary (X:=X) (reserve:=reserve) enum number cf fmt read
local notation3 (prettyPrint := false) "source" => stagedSource B (FieldExport.withSewnFields primary)
local notation3 (prettyPrint := false) "saved" => Retained.Terminal.saved (X:=X) (reserve:=reserve) (Geo:=Geo)
  (a:=shape.sites) (w:=w) (d:=w) fmt

variable (present : Fin shape.edges → Wires Move q d shape.sites shape.edges w b)
local notation3 (prettyPrint := false) "raw" => Grid.physicalOperands G htiles mult hg small F mark present
local notation3 (prettyPrint := false) "past" => stagedHistory (s:=shape.sites) (w:=w)
  (Sewn.terminalHistory (Geo:=Geo) fmt (F).sites raw)

omit [Fintype I] in
/-- The signed packet counts the real scanned site extents, retained bus,
and both exterior-fragment passes at the same physical grid dimensions.
Together they are linear in the actual routing rectangle at fixed word width. -/
theorem signedGridSource_size {L : ℕ} (key : keyWidth q (d+1) ≤ L) (cells : b ≤ L) (bits : w ≤ L)
    (logs : Nat.clog 2 (routingRows shape C J live) ≤ L) :
    (source).size+(saved).size+(past).size ≤ 1900000*routingRows shape C J live*(L+1)^3 := by
  let rows := routingRows shape C J live
  have base : 1+count shape.sites (shape.edges+(p).slots) live C ≤ rows := by
    change 1+count shape.sites (shape.edges+4*(R+1)*tiles) live C ≤ 1+count shape.sites (shape.edges+4*live) live C+J+live
    rw [Nat.mul_assoc 4]
    omega
  have first := frozen_staged_cost (X:=X) (reserve:=reserve) enum number cf fmt read p vf
    host width mark base key cells bits logs
  have last := Grid.staged_physical_history_cubic (Geo:=Geo) G htiles mult hg small shape F mark present fmt J bits logs
  apply (Nat.add_le_add first last).trans
  change 433004*rows*(L+1)^3+1463400*rows*(L+1)^3 ≤ 1900000*rows*(L+1)^3
  rw [←Nat.add_mul,←Nat.add_mul]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI

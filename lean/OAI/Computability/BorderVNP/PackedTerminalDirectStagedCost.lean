import OAI.Computability.BorderVNP.PackedTerminalSewnSelectedAux

/-! # Gate cost of the bare frozen route used by the original-bundle sorter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Cover Cover.AddressCircuit Crossing Packing Packing.CellAddressCircuit Diagonal.ExternalSew FieldExport
open Packing.Inherited.FrozenTape VPVNP.VerifierNetwork

private theorem select_id {X Y : Type} [Fintype X] [Fintype Y] (f : Frame X Y) : f.select id = f := by
  rcases f with ⟨⟨frag,wire⟩⟩
  unfold Frame.select
  congr 2
  funext i
  simp [Function.comp_apply]

variable {I X Move : Type} [Fintype I] [Fintype X] [Fintype Move]
    {q d V E C b w n reserve : ℕ} (enum : Fin q ≃ I)
    (number : (I → Deck (d+1)) ≃ Fin C) (cf : C ≤ 2^b)
    (fmt : Format) (p : Params) (vf : V ≤ 2^w) (host width : Fin n → ℕ) (name : ℕ → ℕ → ℕ)

local notation "RoutePins" => RouteRows.Pins Move q (d+1) V E w
local notation3 (prettyPrint := false) "route" => Retained.Terminal.route (X:=X) (Geo:=RoutePins) (reserve:=reserve) (a:=V) (w:=w) (d:=w) fmt
local notation3 (prettyPrint := false) "extent" => Retained.Terminal.width (X:=X) (Geo:=RoutePins) (reserve:=reserve) (a:=V) (w:=w) (d:=w) fmt true
local notation3 (prettyPrint := false) "fields" => FieldExport.fields (TerminalCells.fields (Move:=Move) (q:=q) (d:=d) (E:=E) vf cf host width) p name

omit [Fintype I] in
/-- Use the raw route and extent outputs directly. Selection by identity
has no effect on wire references, including the two enumerations of the
finite route-pin rectangle. -/
theorem direct_staged_cost {R L : ℕ} (rows : 1+count V (E+p.slots) ((p.R+1)*p.sites) C ≤ R)
    (key : keyWidth q (d+1) ≤ L) (bits : b ≤ L) (word : w ≤ L) (depth : Nat.clog 2 R ≤ L) :
    (stagedSource fields (withSewnFields (boundFrame enum number cf route extent))).size ≤ 433004*R*(L+1)^3 := by
  have total := frozen_staged_cost (Move:=Move) (X:=X) (Geo:=RoutePins) (reserve:=reserve) enum number cf fmt id
    p vf host width name rows key bits word depth
  rw [Retained.Terminal.saved_size,Nat.add_zero] at total
  unfold frozenPrimary at total
  rw [select_id] at total
  exact total

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI

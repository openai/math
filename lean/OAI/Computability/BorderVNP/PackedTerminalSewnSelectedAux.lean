import OAI.Computability.BorderVNP.PackedTerminalAugmentedPins
import OAI.Computability.BorderVNP.PackedTerminalStagedFields
import OAI.Computability.BorderVNP.PackedTerminalEmitterCost

/-! # Cost of the staged private extent on the frozen terminal input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Crossing Cover Cover.AddressCircuit Packing Packing.CellAddressCircuit
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport VPVNP.VerifierNetwork
open Packing.Inherited.FrozenTape
open scoped Classical

variable {I X Geo Move : Type} [Fintype I] [Fintype X] [Fintype Geo] [Fintype Move]
    {q d V E C b w n reserve : ℕ} (enum : Fin q ≃ I)
    (number : (I → Deck (d+1)) ≃ Fin C) (cf : C ≤ 2^b)
    (fmt : Format) (read : RouteRows.Pins Move q (d+1) V E w → Geo)
    (p : Params) (vf : V ≤ 2^w) (host width : Fin n → ℕ) (name : ℕ → ℕ → ℕ)

local notation "Γ" => (X ⊕ Fin reserve) ⊕ fmt.Output Geo V w w
local notation "Z" => Wires Move q d V E w b
local notation3 (prettyPrint := false) "route₀" =>
  (Retained.Terminal.route (X := X) (Geo := Geo) (reserve := reserve) (a := V) (w := w) (d := w) fmt).select read
local notation3 (prettyPrint := false) "width₀" =>
  Retained.Terminal.width (X := X) (Geo := Geo) (reserve := reserve) (a := V) (w := w) (d := w) fmt true

/-- Terminal site owners and retained extents are read from the same
augmented output, using one shared lookup for all the routed site names. -/
noncomputable def frozenPrimary : Frame Γ Z := boundFrame enum number cf route₀ width₀

local notation3 (prettyPrint := false) "primary₀" =>
  frozenPrimary (X := X) (reserve := reserve) enum number cf fmt read
local notation3 (prettyPrint := false) "B₀" =>
  FieldExport.fields (TerminalCells.fields (Move := Move) (q := q) (d := d) (E := E) vf cf host width) p name
local notation3 (prettyPrint := false) "source₀" => stagedSource B₀ (withSewnFields primary₀)
local notation3 (prettyPrint := false) "save₀" =>
  Retained.Terminal.saved (X := X) (Geo := Geo) (reserve := reserve) (a := V) (w := w) (d := w) fmt

omit [Fintype I] in
/-- Reading the saved output needs no gates. The bound includes both the
finite-cover lookup and the incidence scan defining the private extent
after exterior sewing, charged to the actual sewn cable and port rectangle. -/
theorem frozen_staged_cost {R L : ℕ}
    (rows : 1+count V (E+p.slots) ((p.R+1)*p.sites) C ≤ R)
    (key : keyWidth q (d+1) ≤ L) (bits : b ≤ L) (word : w ≤ L) (depth : Nat.clog 2 R ≤ L) :
    (source₀).size + (save₀).size ≤ 433004*R*(L+1)^3 := by
  have room : C+V ≤ R := by unfold count at rows; omega
  have hr : 0<R := by omega
  have owner := owner_cost (E := E) (w := w) (Move := Move) enum number cf room hr key bits depth
  have primary := boundFrame_size enum number cf route₀ width₀
  simp only [Frame.select_size, Retained.Terminal.route_size, Retained.Terminal.width_size, zero_add] at primary
  have pc : (primary₀).size ≤ 1000*R*(L+1)^3+2 := primary.trans (Nat.add_le_add_right owner 2)
  have raw := withSewnFields_size primary₀
  have staged := staged_routing_cost (src := withSewnFields primary₀) B₀ rows word depth
  have positive : 1 ≤ R*(L+1)^3 := Nat.mul_pos hr (pow_pos (Nat.succ_pos L) 3)
  rw [Retained.Terminal.saved_size,Nat.add_zero]
  simp only [Nat.mul_assoc] at staged pc ⊢
  omega

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI

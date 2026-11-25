import OAI.Computability.BorderVNP.DiagonalEnrichedOriginalRowOuter
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGrid
import OAI.Computability.BorderVNP.PackedTerminalGroupedHosts
import OAI.Computability.BorderVNP.PackedTerminalRoutingFields

/-! # Original site selectors on the actual selected machine above the wired grid

The bottom input is the physical grouped seed. The selected geometry
compiler's own rectangular strides determine all retained port addresses.
The immutable private-site selectors and the numeric names of both ends
of each exterior cable are therefore fixed before the profile is supplied.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicCapacity
open BorderVNP.Epoch BorderVNP.Epoch.Round Packing Packing.DeckGrid TeamContraction
open Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts Diagonal.ExternalSew.RowTrace
open EnrichedOuter EnrichedOuter.Boundary TerminalCells
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r t pins link inner n d copies w T : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (compiled : Compiled (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) =>
      copies*inputBlockWidth r n (Fintype.card (Cube D)) d) deep budget cap w)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
    (words : Pins S (d+1) (boundary S (d+1)) w 0 → Bool)
    (good : Good budget 0 (seedState S G d order position copies table words))

local notation "tiles" => tileCount (Fintype.card (Cube D)) d
local notation "leaf" => (Subtype.mk (seedState S G d order position copies table words) good :
  Admissible (Good (S:=S) (start:=d+1) (shape:=boundaryShape S (d+1)) (w:=w)
    (bits:=fun _ : Fin (tileCount (Fintype.card (Cube D)) d) => copies*inputBlockWidth r n (Fintype.card (Cube D)) d) budget) 0)
local notation "leaves" => repeatLeaf (fan S) leaf T
local notation "off" => flatOffset (compiledOffset S (d+1)) T

/-- On every true complete native histogram, the old-port pointer, original
private selector and sewn endpoint name are simultaneously the same physical
row. The immutable selectors only use public schedule data. -/
theorem compiled_grid_names (count : (fan S)^T*copies = R+1)
    (positive : 0<(boundaryShape S (d+1) T).sites)
    (q : (compiled.machine.system.histories T le_rfl leaves).Index) :
    let s := (state (S:=compiled.machine.system) T le_rfl leaves q).val
    let L := (flattenPack T s.pack).layout
    let h := attachedHosts G Fintype.card_pos count L
    (∀ z : Fin ((fan S)^T) × Fin tiles, off z.1+z.2.val = (s.rows.site (L.attach z)).val) ∧
    (∀ z : Fin ((fan S)^T) × Fin tiles, originalPins positive off (finProdFinEquiv z) = s.rows.site (L.attach z)) ∧
    ∀ (u : Fin (R+1)) i, i<tiles → attachedName off copies u.val i = (s.rows.site (h.host (u,i))).val := by
  intro s L h
  have ids (z : Fin ((fan S)^T) × Fin tiles) :
      (s.rows.site (L.attach z)).val = off z.1+z.2.val :=
    compiledRepeated_gridRow compiled leaf (seedState_rows S G d order position copies table words).1 T le_rfl q z
  exact ⟨fun z => (ids z).symm,fun z => originalPin_value positive off z _ (ids z).symm,
    attached_name G Fintype.card_pos count L s.rows.site off ids⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI

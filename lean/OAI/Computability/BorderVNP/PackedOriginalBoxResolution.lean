import OAI.Computability.BorderVNP.CellPacketGeometryOriginalRoster
import OAI.Computability.BorderVNP.PackedProgramBoxRoster
import OAI.Computability.BorderVNP.PackedOriginalDescriptionRows
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # Resolving opaque original boxes at their retained terminal sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse Packet Packing.Inherited

/-- Resolving the original transmission at each retained site and keeping the public
table elsewhere gives the exact padded site array, including empty slots. -/
theorem originalBoxes_resolved {X : Type} {s n : ℕ} (old : Fin n ↪ X) (siteID : X ↪ Fin s)
    (known full : Fin s → List (List Factor)) (body : X → List (List Factor))
    (fs : Fin n → List Factor) (realizes : BoxRoster.Realizes siteID body full)
    (outside : ∀ i, i ∉ Set.range (old.trans siteID) → known i = full i)
    (singleton : ∀ j, body (old j) = [fs j]) (i : Fin s) :
    (originalBoxes (old.trans siteID) known i).map (Source.factors fs) =
      FinalCell.slots siteID body i := by
  rw [realizes.slots_eq]
  cases hi : Function.partialInv (old.trans siteID) i with
  | none =>
    have absent : i ∉ Set.range (old.trans siteID) := by
      rintro ⟨j,rfl⟩
      rw [Function.partialInv_left (old.trans siteID).injective] at hi
      contradiction
    rw [originalBoxes,hi,Option.elim_none,List.map_map]
    change (known i).map id = full i
    simpa only [List.map_id_fun,id_eq] using outside i absent
  | some j =>
    obtain rfl := ((old.trans siteID).injective.isPartialInv j i).mp hi
    rw [originalBoxes_at,show (old.trans siteID) j = siteID (old j) from rfl,realizes.live,singleton]
    rfl

end CellPacketGeometry.History

namespace Diagonal.ExternalSew

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Adaptive PublicCapacity
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open CellSparse Packet CellPacketGeometry.History Inherited
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)]
    {w : ℕ → ℕ → ℕ} {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} (M : EnrichedOuter.Machine.{0,u} deep good V w)
    (rows : ∀ t ht, (M t ht).F.SiteRows) (number : e.Entry → ℕ) (bottom : Admissible good 0)
    (base : Site.Programs bottom.val.pack.layout) (q : (packHistory bottom M.epoch T).Index)
    (dir : Directory.Layout) (count : dir.entries = (fan S)^T*dir.sites)
    (order : Fin dir.sites ≃ bottom.val.pack.layout.Site)

local notation3 "leaf(" j ")" => descriptionOrder bottom.val.pack ((fan S)^T) dir.sites dir.entries count order j
local notation "old" => originalDescriptionRows M bottom q dir count order
local notation3 "siteID" => ((packHistory bottom M.epoch T).term q).val.rows.site
local notation "program" => M.terminalPrivatePrograms rows number bottom base q

/-- A terminal site's original transmission row contains exactly the one-copy
factor tables of the corresponding bottom program. -/
theorem originalDescription_boxes (j : Fin dir.entries) :
    ((program) ((old) j)).program.boxes = (base (leaf(j)).2).program.boxes := by
  rw [Site.Lineage.boxes_eq_birth,Site.Lineage.boxes_eq_birth]
  exact congrArg Site.boxes (M.terminalPrivatePrograms_birth rows number bottom base q (leaf(j)).1 (leaf(j)).2)

/-- In a selected outer history the opaque entries resolve to their original bottom
boxes. The remaining physical rows contain the public factor tables of that history. -/
theorem originalDescription_resolved
    (known full : Fin (shape T).sites → List (List Factor)) (fs : Fin dir.entries → List Factor)
    (realizes : BoxRoster.Realizes (siteID) (fun v => ((program) v).program.boxes) full)
    (outside : ∀ i, i ∉ Set.range ((old).trans (siteID)) → known i = full i)
    (single : ∀ j, (base (leaf(j)).2).program.boxes = [fs j]) (i : Fin (shape T).sites) :
    (originalBoxes ((old).trans (siteID)) known i).map (Source.factors fs) =
      FinalCell.slots (siteID) (fun v => ((program) v).program.boxes) i :=
  originalBoxes_resolved (old) (siteID) known full _ fs realizes outside
    (fun j => (originalDescription_boxes M rows number bottom base q dir count order j).trans (single j)) i

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.PackedBottomCoreChoices
import OAI.Computability.BorderVNP.PackedBottomSupplementRows
import OAI.Computability.BorderVNP.PackedBankSortedCell

/-! # Recovering the original bottom checks in the true final merged cell

The original site's box stays in its table through every retention. At final
placement its real box row moves to the stable merged ordinal and true physical
work prefix. A passing merged observation therefore checks both the original
unary stages and the private zero suffix for every represented copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing CellSparse Inherited CellAddresses BottomGridBank
open scoped Classical

/-- The actual birth site of a report bundle, including the full private box
and the public row that visits all its copies. -/
structure Bundle.Birth (b : Bundle) (s : Site) : Prop where
  /-- Private input, incidence and padding rows are all stored once. -/
  boxes : ∃ wiring : List Factor, s.boxes = [stage b.header.orig b.factors ++ wiring ++
    reportZeros b.header.orig (count b.factors) b.header.cap]
  /-- The compact birth row points at its sole local box. -/
  row : Record.box 0 0 b.header.copies b.header.stride ∈ s.rows
  /-- All old copies occupy the birth site's actual work prefix. -/
  work : b.header.copies*b.header.stride = s.work
  /-- Each reserved original work region ends with its report stage. -/
  stride : b.header.stride = bottomStride b.header.orig b.header.cap
  /-- The private one-copy original source list fits the reserved report region. -/
  capacity : count b.factors ≤ b.header.cap

private theorem oldRows {birth s : Site} (ret : birth.Retention s) : ∀ r ∈ birth.rows, r ∈ s.rows := by
  induction ret with
  | refl => exact fun _ h => h
  | layer prev cuts read cover ih =>
    intro r hr
    rw [Site.retain_rows]
    exact List.mem_append_left _ (ih r hr)
  | forced prev read ih =>
    intro r hr
    rw [SewnField.stage_rows]
    exact List.mem_append_left _ (ih r hr)

variable {D n m p : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin n) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin p)
    (owner : Fin n → ℕ) (state : N.Site → Site) (v : N.Site) (reports : List (List ℕ))
local notation3 "aux" => fun z => (state z).size
local notation3 "offset" => siteBase N cell (cell v) siteID aux ⟨v,rfl⟩
local notation3 "id₀" => FinalCell.firstBox siteID owner state v
local notation3 "dir₀" => FinalCell.directory owner N cell siteID edgeID portID state (cell v) reports

/-- The passed original core of a genuinely retained bottom site is certified
by its actual box in the final directory. No supplemental-use equality has
been used to obtain the original-stage or padding observations. -/
theorem Bundle.corePass_of_retained (b : Bundle) (birth : Site) (matchBirth : b.Birth birth)
    (ret : birth.Retention (state v)) (owned : v ∈ FinalCell.sites siteID owner (cell v))
    (whereAt : b.header.boxBase = offset) (pre : List Bool)
    (room : guessedSize N cell (cell v)+siteSize N cell (cell v) aux ≤ pre.length)
    {os : List (Bool × Option ℕ)} (pass : (dir₀).guardedObservations (lookup pre) = some os) : b.CorePass pre := by
  obtain ⟨wiring,table⟩ := matchBirth.boxes
  have priorTable := (retention_boxes ret).trans table
  have zeroIdx : 0 < (state v).boxes.length := by simp [priorTable]
  have lookupBox := FinalCell.box_get siteID owner state owned 0 zeroIdx
  rw [Nat.add_zero,priorTable] at lookupBox
  have tableAt : (dir₀).boxes.getD id₀ [] =
      stage b.header.orig b.factors ++ wiring ++ reportZeros b.header.orig (count b.factors) b.header.cap :=
    lookupBox
  have row : Record.box id₀ b.header.boxBase b.header.copies b.header.stride ∈ (dir₀).records := by
    refine List.mem_flatMap.mpr ⟨v,owned,List.mem_append_left _ ?_⟩
    refine List.mem_map.mpr ⟨Record.box 0 0 b.header.copies b.header.stride,
      oldRows ret _ matchBirth.row,?_⟩
    simp only [Record.shift,Record.rebaseBox,Nat.add_zero]
    rw [whereAt]
  have span : b.header.boxBase+b.header.copies*b.header.stride ≤ pre.length := by
    rw [whereAt,matchBirth.work]
    exact (Nat.add_le_add_left (ret.work_le.trans (Nat.le_add_right _ _)) _).trans
      ((siteBase_fits N cell (cell v) siteID aux ⟨v,rfl⟩).trans room)
  apply b.corePass_of_guarded pre pass id₀ row _ _ matchBirth.stride matchBirth.capacity span
  · intro f hf
    rw [tableAt]
    exact List.mem_append_left _ (List.mem_append_left _ hf)
  · intro f hf
    rw [tableAt]
    exact List.mem_append_right _ hf

end Packing.BottomReports

end BorderVNP
end Computability
end OAI

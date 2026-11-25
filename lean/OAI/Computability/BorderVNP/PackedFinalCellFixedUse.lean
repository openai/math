import OAI.Computability.BorderVNP.PackedBottomFixedReportCell
import OAI.Computability.BorderVNP.PackedBottomRetainedCorePass
import OAI.Computability.BorderVNP.PackedInheritedMergedOrdinal

/-! # Unique compact use payload of an actual merged physical cell

The owner list can be in any prescribed stable order. Each listed original
has its actual birth and retention proof, and therefore resolves to a checked
box in the pre-supplement directory. The resulting unique payload reads the
same original unary bits in the order consumed by the native reporter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing CellSparse CellAddresses BottomReports
open private mem_padded from OAI.Computability.BorderVNP.PackedInheritedMergedOrdinal
open scoped Classical

variable {D n m p : ℕ} {P J : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin n) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin p)
    (owner : Fin n → ℕ) (aligned : ∀ v, owner (siteID v) = cell v) (state : N.Site → Site)
    (c : ℕ) (reports : List (List ℕ)) (pre : List Bool) (sources : List J) (host : J → N.Site)
    (bundle : J → BottomReports.Bundle) (birth : J → Site)
    (belongs : ∀ j ∈ sources, cell (host j) = c)
    (original : ∀ j ∈ sources, (bundle j).Birth (birth j))
    (retained : ∀ j ∈ sources, Nonempty ((birth j).Retention (state (host j))))
    (start : ∀ j ∈ sources, (bundle j).header.boxBase =
      siteBase N cell (cell (host j)) siteID (fun v => (state v).size) ⟨host j,rfl⟩)
    (room : guessedSize N cell c + siteSize N cell c (fun v => (state v).size) ≤ pre.length)
    {os : List (Bool × Option ℕ)} (pass : (directory owner N cell siteID edgeID portID state c reports).guardedObservations
      (lookup pre) = some os)

include aligned belongs original retained start room pass in
/-- Each real source bundle inherits the passed original stages and private
zero padding from its own stable relocated box in the final directory. -/
theorem retained_use_cores : ∀ b ∈ sources.map bundle, b.CorePass pre := by
  intro b hb
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
  obtain ⟨ret⟩ := retained j hj
  have hc := belongs j hj
  exact (bundle j).corePass_of_retained N cell siteID edgeID portID owner state (host j) reports
    (birth j) (original j hj) ret ((mem_padded N cell (cell (host j)) siteID owner aligned (host j)).mpr rfl)
    (start j hj) pre (by simpa only [hc] using room) (by simpa only [hc] using pass)

include aligned belongs original retained start room pass in
/-- On the genuine checked prefix, the real supplemental rows select exactly
one use list for any fixed preceding count digits. -/
theorem retained_supplements_iff (counts uses : List Bool)
    (width : uses.length = ((sources.map bundle).map BottomReports.Bundle.useBits).sum) :
    (∀ row ∈ supplements (pre.length+counts.length) (sources.map bundle), row.Valid
      (directory owner N cell siteID edgeID portID state c reports).boxes (lookup (pre++counts++uses))) ↔
      uses=useTape pre (sources.map bundle) :=
  supplements_iff_useTape pre counts uses _ _ (retained_use_cores N cell siteID edgeID portID owner aligned
    state c reports pre sources host bundle birth belongs original retained start room pass) width

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI

import OAI.Hierarchy.DescentDatedTerrainAnchor

namespace OAI
/-! # The second original wire of an acquired newborn's pair -/
namespace Hierarchy.DescentOperandPriorIncidence.TerrainAnchor
open DescentSIMDLookup DescentRawCablePanel.DepotRAM DescentPacking.PackedMatch.Local
open scoped Classical Fin.CommRing
noncomputable section

def sibling {n : ℕ} (record : Fin n → Fin 12 → ℕ) (first : ℕ) : Option ℕ :=
  (Stage.matchingRow record true first).map (fun j=>record j 5)

def siblingField (f : Format) (profile outBits : ℕ) (x : Fin f.blocks) (first : Fin f.cap) (i : Fin 5)
    (data : Cell (totalBits f)) : Cell outBits :=
  (sibling (records f profile x (separate f data)) (x.val*(2*f.cap)+first.val)).elim 0 (fun second=>
    (Stage.anchorColumns f.cap (second,0) i:Cell outBits))

theorem sibling_read (f : Format) (profile outBits : ℕ) (x : Fin f.blocks) (first : Fin f.cap) (i : Fin 5)
    (data : Parts f) (second : ℕ)
    (found : sibling (records f profile x data) (x.val*(2*f.cap)+first.val)=some second) :
    siblingField f profile outBits x first i (combine f data)=(Stage.anchorColumns f.cap (second,0) i:Cell outBits) := by
  simp only [siblingField,separate_combine,found,Option.elim_some]

end
end Hierarchy.DescentOperandPriorIncidence.TerrainAnchor

end OAI

import OAI.ThreeFlat.Diagonal.MotifPackedTile

namespace OAI
/-! # The scalar table stored for a physical tile -/

namespace ThreeFlat.RAM.HistoryPartySpecialization
open Diagonal.MotifOrderedCells
noncomputable section
variable {F : Type} [CommRing F] [Fintype F] {e b d : ℕ}

/-- The two archive pointers name the actual bounded tables used at every copy, including
when the current number of copies is zero. -/
def tileTable {H : Type*} (T : Tile F H e d b) : (Fin (b+(e*d+e*d)) → Bool) → F :=
  checkedTile (r:=1) T.rule T.table 0

end
end ThreeFlat.RAM.HistoryPartySpecialization

end OAI

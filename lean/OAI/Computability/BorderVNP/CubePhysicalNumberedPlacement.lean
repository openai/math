import OAI.Computability.BorderVNP.CubePhysicalNumberedRows
import OAI.Computability.BorderVNP.DiagonalPhysicalAssignments
import OAI.Computability.BorderVNP.DiagonalAssignedRows
import OAI.Computability.BorderVNP.BranchAdviceBitsTable

/-! # Numbered native rows at the public placement selected by an assigned path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.PacketPlacement

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical
open scoped Classical BigOperators

variable {D n d b h K s B T H U : ℕ} {P Team Param Gadget : Type} {bits : P → ℕ} {N : Network D P bits}
    [Fintype Team] [Fintype Param]
    (packet : PacketPlacement Team n d b h K N) (t : Tracked Team Param Gadget B N) (x : Ports bits)
    (pos : TableEntry n b h K s → Gadget) (v : packet.Passing t x pos)
    (team : Team ≃ Fin T) (param : Param ≃ Fin H) (scalar : Gadget ≃ Fin U)

/-- A row indexed by the current owner, on the native columns for the
actual finite scalar and parameter arrays of this placement. -/
noncomputable def nativeRow :=
  physicalRow packet.slot (numberTables param scalar t.tags) x (fun _ => scalar ∘ pos) (t.words.number team param scalar)
    packet.label (team ∘ packet.team v.val.2.2.2.1) v.val

/-- Finite table indexing changes only the names of the original slots and
the scalar coordinates. -/
theorem numbered_pathTally :
    pathTally packet.slot (numberTables param scalar t.tags) x (fun _ => scalar ∘ pos) (t.words.number team param scalar)
      packet.label (team ∘ packet.team v.val.2.2.2.1) v.val =
    ((packet.tally t x pos v).renumber team param).numberScalars scalar :=
  pathTally_number packet.slot t.tags x (fun _ => pos) t.words packet.label (packet.team v.val.2.2.2.1)
    v.val team param scalar

/-- Sum all actual native owner rows into the batch-indexed formal tally. -/
theorem nativeRow_sum (j : Fin (H+U)) :
    (∑ i, packet.nativeRow t x pos v team param scalar i j) =
    ∑ i, DiagonalTallyRAM.tallyRow (((packet.tally t x pos v).renumber team param).numberScalars scalar) i j :=
  sum_numbered_physicalRow packet.slot t.tags x (fun _ => pos) t.words packet.label (packet.team v.val.2.2.2.1)
    v.val team param scalar j

end Diagonal.CellEntries.PacketPlacement

namespace Diagonal.CellEntries.Assigned

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical ParseTable
open scoped Classical BigOperators

variable {D n d b h K s B T k size U : ℕ}
    {Team Gadget History Hidden Pin : Type} [Fintype Team]
    {Port : History → Type} {width : (q : History) → Port q → ℕ}
    (N : (q : History) → Network D (Port q) (width q))
    (packet : ∀ q, PacketPlacement Team n d b h K (N q))
    (tags : ∀ q, Hidden → Tracked Team (PairedParameters k size) Gadget B (N q))
    (pin : Pin → ∀ q, Ports (width q)) (pos : TableEntry n b h K s → Gadget)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (teams : Team ≃ Fin T) (scalar : Gadget ≃ Fin U)
    (i : Pin) (v : Path N packet tags pin pos i)

/-- Current-owner subtotals on the realized public history and hidden assignment. -/
noncomputable def nativeRow :=
  (packet v.1).nativeRow (tags v.1 v.2.1) (pin i v.1) pos v.2.2 teams (numberedLabelEquiv ord k size) scalar

/-- The path tally using the complete original slot numbering and numbered scalar directory. -/
noncomputable def nativePathTally :=
  let t := tags v.1 v.2.1
  let pl := packet v.1
  let params := numberedLabelEquiv ord k size
  pathTally pl.slot (numberTables params scalar t.tags) (pin i v.1) (fun _ => scalar ∘ pos)
    (t.words.number teams params scalar) pl.label (teams ∘ pl.team v.2.2.val.2.2.2.1) v.2.2.val

theorem nativeTally_eq :
    nativePathTally N packet tags pin pos ord teams scalar i v =
    (numbered N packet tags pin pos ord teams i v).numberScalars scalar :=
  (packet v.1).numbered_pathTally (tags v.1 v.2.1) (pin i v.1) pos v.2.2 teams (numberedLabelEquiv ord k size) scalar

theorem nativeRow_sum (j : Fin (Branch.pairedTableParameters (k+1) size+U)) :
    (∑ a, nativeRow N packet tags pin pos ord teams scalar i v a j) =
    ∑ a, DiagonalTallyRAM.tallyRow ((numbered N packet tags pin pos ord teams i v).numberScalars scalar) a j :=
  (packet v.1).nativeRow_sum (tags v.1 v.2.1) (pin i v.1) pos v.2.2 teams (numberedLabelEquiv ord k size) scalar j

end Diagonal.CellEntries.Assigned

end BorderVNP
end Computability
end OAI

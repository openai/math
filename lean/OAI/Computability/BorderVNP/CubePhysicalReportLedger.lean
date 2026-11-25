import OAI.Computability.BorderVNP.CubePhysicalCellOperandOrder

/-! # The complete emitted report and cube descriptor list has the physical path tally

A private cell checks its own reported digit addresses while the scanner uses
absolute RAM addresses. The two operands are compared only by their coordinate
and natural value. The proof also permits repeated, equal cube IDs and zero
unary increments at different true report positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open Crossing Diagonal Diagonal.CellEntries DiagonalTallyMaterialize DiagonalTallyCellReports
open scoped BigOperators Classical

variable {l : ReportLayout} {n d blocks b h K s D B T : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell] {N : Network D P bits} {cell : N.Site → Cell}
variable (tags : N.Tables (Entry (Fin l.parameters) (Fin l.gadgets)))
    (pos : Packet n d blocks → TableEntry n b h K s → Fin l.gadgets)
    (words : PowerWords (Fin T) (Fin l.parameters) (Fin l.gadgets) B N tags)
    (label : Cell → Label (n+1) d) (team : Fin d → Fin T)
    (a : Path N cell n d blocks b h K s) (t : Fin T)
    (o : Orders tags words label team a t)
    (uses : PowerSlot (Fin T) (Fin l.parameters) B → UseRead)
    (cells : ∀ c : Cell, CellRead {v : N.Site // cell v = c} l.gadgets)
    (packets : Packet n d blocks × Vertex (n+1) → PacketRead)
    (reports : Cell → ReportCell l)

/-- The actual compact team-cell enumeration used by its native report writer. -/
noncomputable abbrev teamReports := List.ofFn fun j => reports (o.cells j).val

omit [DecidableEq Cell] [Fintype Cell] in
/-- Every checked physical count row has the same arithmetic content as the
relative digit words of the merged private checker. -/
theorem reportCountPairs (c : Cell)
    (fields : (cells c).directory.reportedCounts =
      countFields ((reports c).privateWires+(reports c).supplied) l.gadgets l.countWidth)
    (data : ∀ g j, (reports c).counts g j =
      (cells c).bank ((reports c).privateWires+(reports c).supplied+g.val*l.countWidth+j.val))
    (q : ReportCursor) :
    (reports c).countPairs = List.ofFn fun g => ((cells c).operand l.parameters g).pair := by
  apply congrArg List.ofFn
  funext g
  let f := (reports c).countFrame q
  exact (f.count_pair g ((reports c).counts g)).symm.trans
    ((countPair_siteSum (reports c) (cells c) fields data g q).trans ((cells c).operand_pair l.parameters g).symm)

omit [Fintype Cell] [DecidableEq Cell] in
/-- The true native chronological descriptor list can be used directly in
the allocated natural tally theorem. Its reported count fields are forced by the
passing private directory, its unary slots are identified once each in the physical
sidecars and its last words are the actual routed packet lookups. -/
theorem emittedPairs_perm (q : ReportCursor) (cube : Fin o.nVertex → Operand)
    (source : UseOccurrence (teamReports tags words label team a t o reports) ≃
      {i // routedPowerOwner tags words label team a i = t})
    (align : ∀ u, let i := (source u).val
      occurrencePair (teamReports tags words label team a t o reports) u =
        (i.2.1.val,if (uses i).bit then 2^i.2.2.val else 0))
    (fields : ∀ c, (cells c).directory.reportedCounts =
      countFields ((reports c).privateWires+(reports c).supplied) l.gadgets l.countWidth)
    (data : ∀ c g j, (reports c).counts g j =
      (cells c).bank ((reports c).privateWires+(reports c).supplied+g.val*l.countWidth+j.val))
    (lookup : ∀ j, (cube j).pair = (l.parameters+(pathPacketID pos a (o.vertices j).val).val,1)) :
    ((cellOperands (teamReports tags words label team a t o reports) q ++ List.ofFn cube).map Operand.pair).Perm
      ((operands tags pos words label team a t o uses cells packets).map Operand.pair) := by
  let cs := teamReports tags words label team a t o reports
  let val := fun i : {i // routedPowerOwner tags words label team a i = t} =>
    (i.val.2.1.val,if (uses i.val).bit then 2^i.val.2.2.val else 0)
  have hu := usePairs_perm cs source o.uses val align
  have hc : cs.flatMap ReportCell.countPairs =
      (List.ofFn fun j => List.ofFn fun g => ((cells (o.cells j).val).operand l.parameters g).pair).flatten := by
    rw [List.flatMap_def,List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    exact reportCountPairs cells reports _ (fields _) (data _) q
  have hp : (List.ofFn cube).map Operand.pair =
      List.ofFn fun j => (l.parameters+(pathPacketID pos a (o.vertices j).val).val,1) := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext lookup)
  rw [List.map_append,hp,operands]
  simp only [List.map_append,List.map_flatten,List.map_ofFn,Function.comp_def,unaryOperand_pair,packetOperand_pair]
  apply List.Perm.append_right
  apply (cellOperands_pairs_perm cs q).trans
  rw [hc]
  exact hu.append_right _

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI

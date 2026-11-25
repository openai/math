import OAI.Computability.BorderVNP.CubePhysicalReportReaders
import OAI.Computability.BorderVNP.DiagonalReceivedReportUseReadback
import OAI.Computability.BorderVNP.DiagonalReceivedCellScalarRead

/-! # Complete scalar readers on the decoded physical path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries CellSparse
open DiagonalTallyCellReports
open scoped Classical

variable {D ns ne np C T : ℕ} {P J Param Gadget Team : Type} [Fintype P]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (shape : ∀ j,(state (host j)).birth.work=mult j*(slabs j).stride)
    {n d blocks b h K s : ℕ} (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (tags : BottomChoices slabs mult → N.Tables (Entry Param Gadget))
    (owner : Fin ns → ℕ) (ho : ∀ v, owner (siteID v)=(cell v).val)
    (birthLocal : ∀ v, (state v).birth.Local) (schema : ∀ v, (state v).program.Schema)
    (relative : ∀ v, (state v).program.RelativeBoxes)
    (bottom : Fin C → List Bundle) (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)
    {l : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)

    (param : Param ≃ Fin l.parameters) (scalar : Gadget ≃ Fin l.gadgets)
    (ok : ∀ z,TagModels N edgeID portID state (tags z) (scalar.toEmbedding.trans Fin.valEmbedding)
      (carryPred host (birthPredicate slabs mult z)))
    (tape : Fin T → ℕ → Bool) (start : Fin T → ℕ)
local notation3 (prettyPrint := false) "src" j => R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw (j).1 (j).2
local notation3 (prettyPrint := false) "steps" => (t : Fin T) × Fin (R.cells t).length
local notation3 (prettyPrint := false) "typed" => R.reportedWithTape tape start
local notation3 (prettyPrint := false) "z₀" => extractBottom N cell siteID (placedSize N state) owners slabs mult
  (fun _ j => retainedLocation N state host slabs mult shape j) q raw
local notation3 (prettyPrint := false) "path" => rawPath N cell edgeID state owners q raw

include ho birthLocal schema relative ok in
/-- At every public cell number use its actual per-team count cursor and the
scalar words checked on that same returned private path. -/
noncomputable def ReceivedRows.scalarReaders {w order : ℕ} (first : Fin T → ReportCursor)
    (pass : ∀ j : steps,(src j).Passing w order)
    (returns : ∀ j : steps,∃ ret,(src j).Returns w order (typed (R.order j)) ret)
    (size : ∀ j : steps, ((R.cells j.1).get j.2).privateWires+((R.cells j.1).get j.2).supplied =
      (src j).privateWires+(src j).boundary.length) :
    NativeLedger.ReportCellReaders slot (numberTables param scalar (tags z₀)) ports path typed := by
  classical
  let refs (c : Fin C) (g : Fin l.gadgets) :=
    let j := R.order.symm c
    let cs := tapeCells (tape j.1) (start j.1) (R.cells j.1)
    let prior := (cs.take j.2.val).foldl (fun q r => r.after q) (first j.1)
    prior.refs+g.val*l.countWidth
  have rests (c : Fin C) : ∃ read : NativeLedger.CellRead {v : N.Site // cell v=c} l.gadgets,
      read.directory.reportedCounts = countFields ((typed c).privateWires+(typed c).supplied) l.gadgets l.countWidth ∧
      (∀ g j,(typed c).counts g j=read.bank ((typed c).privateWires+(typed c).supplied+g.val*l.countWidth+j.val)) ∧
      ∀ v g,((read.observed v).filterMap Prod.snd).count g.val =
        (counters (numberTables param scalar (tags z₀) v.val (pathEdges slot path v.val) (fun i => ports i.val))).2 g := by
    obtain ⟨j,rfl⟩ := R.order.surjective c
    obtain ⟨ret,run⟩ := returns j
    let offset := start j.1+(((R.cells j.1).take j.2.val).map ReportCell.tailWidth).sum
    have eq : typed (R.order j)=((R.cells j.1).get j.2).withTape (tape j.1) offset :=
      R.reportedWithTape_at tape start j.1 j.2
    rw [eq] at run ⊢
    obtain ⟨read,_,_,fields,digits,observed⟩ := R.scalar_operands_of_return N cell siteID edgeID portID state host
      slabs mult shape owners slot ports tags owner ho birthLocal schema relative bottom q raw j.1 j.2
      param scalar ok (pass j) (tape j.1) offset ret run (refs (R.order j)) (size j)
    exact ⟨read,fields,digits,observed⟩
  exact ⟨fun c => (rests c).choose,fun c => (rests c).choose_spec.2.2,fun c => (rests c).choose_spec.1,
    fun c => (rests c).choose_spec.2.1⟩

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

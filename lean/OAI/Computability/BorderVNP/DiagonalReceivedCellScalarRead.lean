import OAI.Computability.BorderVNP.DiagonalNativeCellScalarRead
import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived

/-! # The returned scalar ledger at the selected native team and cell ordinal -/

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
    {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
    (u : Fin T) (i : Fin (R.cells u).length)
    (param : Param ≃ Fin (layout u).parameters) (scalar : Gadget ≃ Fin (layout u).gadgets)
    (ok : ∀ z,TagModels N edgeID portID state (tags z) (scalar.toEmbedding.trans Fin.valEmbedding)
      (carryPred host (birthPredicate slabs mult z)))
local notation3 (prettyPrint := false) "src" => R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw u i
local notation3 (prettyPrint := false) "atCell" => R.order ⟨u,i⟩
local notation3 (prettyPrint := false) "z₀" => extractBottom N cell siteID (placedSize N state) owners slabs mult
  (fun _ j => retainedLocation N state host slabs mult shape j) q raw
local notation3 (prettyPrint := false) "path" => rawPath N cell edgeID state owners q raw

include ho birthLocal schema relative ok in
/-- The private source prefix and count directory are those of the visited cell
in the actual report table. Canonical counted reports thus yield a scalar readout
for its decoded full path, with the same native report offsets. -/
theorem ReceivedRows.returned_scalar_operands {w order : ℕ} (pass : (src).Passing w order)
    (report : ReportCell (layout u)) (canonical : report.bits=(src).spelling) (refs : Fin (layout u).gadgets → ℕ)
    (size : report.privateWires+report.supplied=(src).privateWires+(src).boundary.length) :
    ∃ read : NativeLedger.CellRead {v : N.Site // cell v=atCell} (layout u).gadgets,
      read.directory=(src).initial ∧ read.bank=lookup ((src).pre++report.bits) ∧
      read.directory.reportedCounts=countFields (report.privateWires+report.supplied) (layout u).gadgets (layout u).countWidth ∧
      (∀ g k, report.counts g k=read.bank (report.privateWires+report.supplied+g.val*(layout u).countWidth+k.val)) ∧
      ∀ v g, ((read.observed v).filterMap Prod.snd).count g.val =
        (counters (numberTables param scalar (tags z₀) v.val (pathEdges slot path v.val) (fun a => ports a.val))).2 g := by
  have orig := R.assignedAt_directory N cell siteID edgeID portID state owners slot ports owner bottom q raw u i
  apply returned_scalar_read N cell siteID edgeID portID state host slabs mult shape owners slot ports tags q atCell raw
    owner ho birthLocal schema relative (layout u) src pass report canonical refs param scalar ok _ _ size
  · rw [orig]
    rfl
  · exact R.assignedAt_pre N cell siteID edgeID portID state owners slot ports owner bottom q raw u i

local notation3 (prettyPrint := false) "original" => (R.cells u).get i

/-- An individual returned private call on its actual assigned tape certifies
its own canonical spelling. This includes all zero count words and read bits. -/
theorem ReceivedRows.scalar_return_spelling {w order : ℕ} (pass : (src).Passing w order)
    (tape : ℕ → Bool) (start : ℕ) (ret : List Bool × Bool)
    (returns : (src).Returns w order ((original).withTape tape start) ret) :
    ((original).withTape tape start).bits=(src).spelling := by
  obtain ⟨_,classify⟩ := (src).native w order pass
  exact ((classify tape start ret).mp returns).1

include ho birthLocal schema relative ok in
/-- Read every scalar and all of its actual relative digit pointers on a genuine
return of the original runtime checker. The accepted tape supplies the report words. -/
theorem ReceivedRows.scalar_operands_of_return {w order : ℕ} (pass : (src).Passing w order)
    (tape : ℕ → Bool) (start : ℕ) (ret : List Bool × Bool)
    (returns : (src).Returns w order ((original).withTape tape start) ret)
    (refs : Fin (layout u).gadgets → ℕ)
    (extent : (original).privateWires+(original).supplied=(src).privateWires+(src).boundary.length) :
    let report := (original).withTape tape start
    ∃ read : NativeLedger.CellRead {v : N.Site // cell v=atCell} (layout u).gadgets,
      read.directory=(src).initial ∧ read.bank=lookup ((src).pre++report.bits) ∧
      read.directory.reportedCounts=countFields (report.privateWires+report.supplied) (layout u).gadgets (layout u).countWidth ∧
      (∀ g k, report.counts g k=read.bank (report.privateWires+report.supplied+g.val*(layout u).countWidth+k.val)) ∧
      ∀ v g, ((read.observed v).filterMap Prod.snd).count g.val=
        (counters (numberTables param scalar (tags z₀) v.val (pathEdges slot path v.val) (fun a => ports a.val))).2 g := by
  intro report
  exact R.returned_scalar_operands N cell siteID edgeID portID state host slabs mult shape owners slot ports tags owner
    ho birthLocal schema relative bottom q raw u i param scalar ok pass report
    (R.scalar_return_spelling N cell siteID edgeID portID state owners slot ports owner bottom q raw u i
      pass tape start ret returns) refs extent

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

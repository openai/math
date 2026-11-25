import OAI.Computability.BorderVNP.DiagonalNativeCorePaths
import OAI.Computability.BorderVNP.CubePhysicalReturnedCellRead
import OAI.Computability.BorderVNP.DiagonalNativeNumbering

/-! # Scalar identifiers counted on a returning assigned signed path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs Diagonal.CellEntries CellSparse
open scoped Classical

variable {D ns ne np C : ℕ} {P J Param Gadget : Type} [Fintype P]
    {bits' : P → ℕ} (N : Network D P bits') (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)
    {n d blocks b h K s : ℕ} {Team : Type}
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits')
    {H U : ℕ} (param : Param ≃ Fin H) (scalar : Gadget ≃ Fin U) (tags : BottomChoices slabs mult → N.Tables (Entry Param Gadget))
    (model : ∀ z, TagModels N edgeID portID state (tags z) (scalar.toEmbedding.trans Fin.valEmbedding) (carryPred host (birthPredicate slabs mult z)))
    (q : Routed (b:=b) (s:=s) owners) (c : Fin C)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)

local notation3 (prettyPrint := false) "number" => scalar.toEmbedding.trans Fin.valEmbedding
local notation3 (prettyPrint := false) "supply" => pathSupply N cell edgeID portID owners slot ports
local notation3 (prettyPrint := false) "size" => placedSize N state
local notation3 (prettyPrint := false) "whereAt" => (fun (_ : Routed (b:=b) (s:=s) owners) j => retainedLocation N state host slabs mult birthWidth j)
local notation3 (prettyPrint := false) "z" => extractBottom N cell siteID size owners slabs mult whereAt q raw
local notation3 (prettyPrint := false) "g" => privateWires N cell size c (raw c)
local notation3 (prettyPrint := false) "a" => privateStaging N cell size c (raw c)
local notation3 (prettyPrint := false) "here" => tagReadAt N cell edgeID portID state host slabs mult owners supply number tags model z q c g
local notation3 (prettyPrint := false) "entry" => (fun v : {v : N.Site // cell v=c} =>
  tags z v.val (localWire N cell edgeID portID owners supply q c g v) (localPort N cell edgeID portID owners supply q c v))

variable (owner : Fin ns → ℕ) (ho : ∀ v,owner (siteID v)=(cell v).val)
    (birthLocal : ∀ v, (state v).birth.Local) (schema : ∀ v, (state v).program.Schema)
    (relative : ∀ v,(state v).program.RelativeBoxes)
local notation3 (prettyPrint := false) "chunks" => fun v : {v : N.Site // cell v=c} => (here v).observations
local notation3 (prettyPrint := false) "current" => rawPath N cell edgeID state owners q raw
local notation3 (prettyPrint := false) "ntags" => numberTables param scalar (tags z)

include ho birthLocal schema relative in
/-- A genuine guarded return supplies both the site order of the native scalar
reports and their exact frequency at each number in the mathematical tagged table.
The private wire and both supplied endpoint words are read from this same routed path. -/
theorem scalarRows_of_guarded (reports : List (List ℕ)) (out : List (Bool × Option ℕ))
    (guarded : (FinalCell.directory owner N (fun v => (cell v).val) siteID edgeID portID
      (fun v => (state v).program) c.val reports).guardedObservations
      (lookup (bank N cell c size g a (supply q c))) = some out) :
    (List.ofFn (NativeLedger.cellSiteOrder cell siteID owner ho c)).flatMap chunks = out ∧
      ∀ (v : {v : N.Site // cell v=c}) (j : Fin U), ((chunks v).filterMap Prod.snd).count j.val =
        (counters (ntags v.val (pathEdges slot current v.val) (fun t => ports t.val))).2 j := by
  obtain ⟨flat,nz,_⟩ := (tagged_native_cell_guard N cell siteID edgeID portID state host slabs mult birthWidth
    owners supply number tags model q c raw owner reports ho birthLocal schema relative out).mp guarded
  refine ⟨(NativeLedger.cellSiteOrder_flatMap cell siteID owner ho c chunks).trans flat,?_⟩
  intro v j
  have freq := (here v).count (nz v) (scalar.symm j)
  have eq : number (scalar.symm j) = j.val := congrArg Fin.val (scalar.apply_symm_apply j)
  rw [eq] at freq
  have same := congrArg₂ (tags z v.val) (localWire_path N cell edgeID portID state owners slot ports q raw c v)
    (localPort_path N cell edgeID portID owners slot ports q c v)
  change _ = (counters (numberEntry param scalar (tags z v.val (pathEdges slot current v.val)
    (fun t => ports t.val)))).2 j
  rw [counters_numberEntry,Finsupp.mapDomain_equiv_apply]
  exact freq.trans (congrArg (fun u => (counters u).2 (scalar.symm j)) same)

open DiagonalTallyCellReports
variable (l : ReportLayout)

include ho birthLocal schema relative in
/-- A canonical cell return gives all three per-cell inputs to the signed
finish: the sorted scalar observations, the source count directory, and the
actual reported bits read back by the public writer. -/
theorem returned_scalar_read {w n₀ : ℕ} (src : AssignedCell l) (pass : src.Passing w n₀)
    (report : ReportCell l) (canonical : report.bits=src.spelling) (refs : Fin l.gadgets → ℕ)
    (param : Param ≃ Fin l.parameters) (gadget : Gadget ≃ Fin l.gadgets)
    (ok : ∀ witness, TagModels N edgeID portID state (tags witness) (gadget.toEmbedding.trans Fin.valEmbedding)
      (carryPred host (birthPredicate slabs mult witness)))
    (old : src.initial=FinalCell.directory owner N (fun v => (cell v).val) siteID edgeID portID
      (fun v => (state v).program) c.val src.initial.reportedCounts)
    (initial : src.pre=bank N cell c size g a (supply q c))
    (prefixSize : report.privateWires+report.supplied=src.privateWires+src.boundary.length) :
    ∃ read : NativeLedger.CellRead {v : N.Site // cell v=c} l.gadgets,
      read.directory=src.initial ∧ read.bank=lookup (src.pre++report.bits) ∧
      read.directory.reportedCounts=countFields (report.privateWires+report.supplied) l.gadgets l.countWidth ∧
      (∀ gid j, report.counts gid j=read.bank (report.privateWires+report.supplied+gid.val*l.countWidth+j.val)) ∧
      ∀ v j, ((read.observed v).filterMap Prod.snd).count j.val=
        (counters ((numberTables param gadget (tags z)) v.val (pathEdges slot current v.val)
          (fun t => ports t.val))).2 j := by
  let obs := fun v : {v : N.Site // cell v=c} => (tagReadAt N cell edgeID portID state host slabs mult owners supply
    (gadget.toEmbedding.trans Fin.valEmbedding) tags ok z q c g v).observations
  have guard := pass.seen []
  simp only [List.append_nil] at guard
  rw [initial] at guard
  have native := congrArg (fun dir : Directory => dir.guardedObservations (lookup (bank N cell c size g a (supply q c)))) old
  have facts := scalarRows_of_guarded N cell siteID edgeID portID state host slabs mult birthWidth owners slot ports
    param gadget tags ok q c raw owner ho birthLocal schema relative src.initial.reportedCounts src.observations
    (native.symm.trans guard)
  have parts := (NativeLedger.cellSiteOrder_flatMap cell siteID owner ho c obs).symm.trans facts.1
  let read := NativeLedger.returnedCellRead cell siteID owner ho c src pass report canonical obs parts refs
  have h := NativeLedger.returnedCellRead_fields cell siteID owner ho c src pass report canonical obs parts refs prefixSize
  exact ⟨read,rfl,rfl,h.1,h.2,facts.2⟩

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI

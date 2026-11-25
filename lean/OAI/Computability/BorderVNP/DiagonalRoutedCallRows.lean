import OAI.Computability.BorderVNP.DiagonalSourceReceivedRows
import OAI.Computability.BorderVNP.DiagonalNativeJoinedRows
import OAI.Computability.BorderVNP.DiagonalNativeCellRoster

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Reading the routed source row through its actual global call ordinal -/

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM Crossing CellDispatch CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments
open DiagonalTallyCellReports ReportDirectory
open scoped Classical

variable {R J : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (label : Fin ar.cells → Label (ar.n+1) ar.header.d)
    (charts : Fin (R+1) → ReportLayout) (home : Fin J → Fin ar.cells) (bodies : Fin J → ReportBundle)
    (supplied wires : ℕ → ℕ) (q : Routed (b:=ar.b) (s:=ar.s) owners)
local notation3 (prettyPrint := false) "routed" => routedReceivedRows ar owners label charts home bodies supplied wires q
local notation3 (prettyPrint := false) "own" => fun c => owners q.1 (label c (chosen ar.b ar.s q.1))
local notation3 (prettyPrint := false) "bank" => fun c => ar.cellBank+c*ar.cellStride

/-- All fields of an original routed cell are fixed by its actual global
ordinal, including its empty initial report digits and exact per-cell sidecars. -/
theorem routedReceivedRow (u : Fin (R+1)) (i : Fin ((routed).cells u).length) :
    ((routed).cells u).get i =
      sourceCell (charts u) home bodies bank supplied wires (fun _ _ _ => false) ((routed).order ⟨u,i⟩).val := by
  let old := ((routed).cells u).get i
  let src := sourceCell (charts u) home bodies bank supplied wires (fun _ _ _ => false)
  have mem := List.get_mem ((routed).cells u) i
  change old ∈ ((List.range ar.cells).filter fun c => decide (routedOwnerWord ar owners label q c=u.val)).map src at mem
  obtain ⟨n,_,e⟩ := List.mem_map.mp mem
  have key : n=((routed).order ⟨u,i⟩).val :=
    (congrArg ReportCell.number e).trans ((routed).number u i)
  exact e.symm.trans (congrArg src key)

/-- An actual post-builder owner table for the selected cube gives an occupied
dispatch entry for every source row of the native preparing equivalence. -/
theorem routedDispatch {w n : ℕ} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {gen : Fragment IO}
    (S : Fin (R+1) → PositiveTeam id gen n w) (p : ∀ u,(S u).Prefix) (calls : ℕ)
    (table : ∀ u, OwnerTable (S u).pub ((S u).postMemory (p u)) ⟨u.val,calls,ar.cells⟩ (PositiveTeam.ownerWord own))
    (u : Fin (R+1)) (i : Fin ((routed).cells u).length) :
    let c := (routed).order ⟨u,i⟩
    let f := Frame.ofMemory (S u).pub ((S u).postMemory (p u))
    c.val<f.count ∧ readings ((S u).postMemory (p u)) (f.address c.val)=f.team := by
  intro c f
  have owns := receivedSourceRows_owner charts home bodies own (routedOwnerWord ar owners label q)
    (routedOwnerWord_at ar owners label q) bank supplied wires (fun _ _ _ _ => false) u i
  have word := (table u).atRow c.val c.isLt
  rw [PositiveTeam.ownerWord,dite_eq_left c.isLt] at word
  have same : f=⟨u.val,calls,ar.cells⟩ := (table u).frame
  rw [same]
  exact ⟨c.isLt,word.trans (congrArg Fin.val owns)⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI

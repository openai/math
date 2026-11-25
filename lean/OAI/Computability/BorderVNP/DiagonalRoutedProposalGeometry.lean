import OAI.Computability.BorderVNP.DiagonalRoutedCallRows
import OAI.Computability.BorderVNP.DiagonalNativeReportBindings

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Original cell coordinates of every proposed signed report on the routed word packet -/

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

/-- Choosing any report count or use-bit tape retains its original global
number, external address and width of the supplied part of that cell. -/
theorem routedProposedCoordinates (u : Fin (R+1)) (rows : ReportAssignments ((routed).cells u))
    (i : Fin ((routed).cells u).length) :
    let r := rows.val.get (Fin.cast rows.length.symm i)
    let c := (routed).order ⟨u,i⟩
    r.number=c.val ∧ r.external=ar.cellBank+c.val*ar.cellStride ∧ r.supplied=supplied c.val := by
  intro r c
  let fields (row : ReportCell (charts u)) := (row.number,row.external,row.supplied)
  have captured := congrArg fields (rows.row_eq i)
  have fixed := congrArg fields (routedReceivedRow ar owners label charts home bodies supplied wires q u i)
  have eq : fields r=(c.val,ar.cellBank+c.val*ar.cellStride,supplied c.val) := captured.trans fixed
  exact ⟨congrArg Prod.fst eq,congrArg (fun x => x.2.1) eq,congrArg (fun x => x.2.2) eq⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI

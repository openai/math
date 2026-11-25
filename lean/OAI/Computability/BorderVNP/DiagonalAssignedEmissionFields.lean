import OAI.Computability.BorderVNP.DiagonalEmittedReceivedNumber
import OAI.Computability.BorderVNP.DiagonalSignedGlobalSparseLaunch

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Original sparse cell values and their report ordinals -/

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM DiagonalTallyCellReports Cube.Physical.NativeAssignments Evaluator TypedTaskBuilder

variable {w T : ℕ} {a : SignedTaskArena.Layout} {f : Layout} {m : Memory w}
    {fit : f.Fits w (readings m)} {cc : a.fragments.cells=f.cells} (e : SparseEmission a f m fit cc)
    {charts : Fin T → ReportLayout} (R : ReceivedRows charts a.cube.cells) (u : Fin T)
    (payload : ReportAssignments (R.cells u)) (frame offsets ctl live ports : ℕ)
    (data : ℕ → ℕ → Bool) (width : ℕ → ℕ) (inputs : Fin a.cube.cells → List Bool)
local notation3 (prettyPrint := false) "scan" => a.controlRows u.val frame offsets ctl live ports
local notation3 (prettyPrint := false) "out" => readings e.output
local notation3 (prettyPrint := false) "number" => (scan).before out (scan).cells
local notation3 (prettyPrint := false) "globals" r => e.globalCells (a:=a) (team:=u.val) (frame:=frame)
  (offsets:=offsets) (ctl:=ctl) («live»:=live) (ports:=ports) r

/-- Every physical compact cell refers to the right original row, beginning with its true
incoming bits and continuing with its chronological count and use choices. -/
def SparseEmission.AssignedFields : Prop :=
  ∃ size : number=(R.cells u).length, ∃ rows : (i : Fin number) → SparseCell a f m data i.val,
    (∀ j, (rows j).number.val=globalCell (scan).toLayout out j.val) ∧
    (∀ j, (rows j).number=R.order ⟨u,Fin.cast size j⟩ ∧
      (rows j).tail=(payload.val.get (Fin.cast payload.length.symm (Fin.cast size j))).bits) ∧
    (∀ j, (readings m) (f.supplied+(rows j).number.val)=width (rows j).number.val) ∧
    ∀ i : Fin (R.cells u).length, let c := R.order ⟨u,i⟩
      (((globals rows) c.val).field).values=inputs c++(payload.val.get (Fin.cast payload.length.symm i)).bits

variable {e R u payload frame offsets ctl live ports data width inputs}

/-- Expose the data of the emitted report and its original row number from the same witnesses. -/
theorem SparseEmission.AssignedFields.withOrdinals
    (h : e.AssignedFields R u payload frame offsets ctl live ports data width inputs) :
    ∃ size : number=(R.cells u).length, ∃ bytes : ℕ → ℕ → Bool,
      ∃ rows : (i : Fin number) → SparseCell a f m bytes i.val,
      (∀ j, (rows j).number.val=globalCell (scan).toLayout out j.val) ∧
      (∀ j, (rows j).number=R.order ⟨u,Fin.cast size j⟩ ∧
        (rows j).tail=(payload.val.get (Fin.cast payload.length.symm (Fin.cast size j))).bits) ∧
      (∀ j, (readings m) (f.supplied+(rows j).number.val)=width (rows j).number.val) ∧
      (∀ i : Fin (R.cells u).length, let c := R.order ⟨u,i⟩
        (((globals rows) c.val).field).values=inputs c++(payload.val.get (Fin.cast payload.length.symm i)).bits) ∧
      ∀ i : Fin (R.cells u).length, (R.cells u)[i].number=globalCell (scan).toLayout out i.val := by
  obtain ⟨size,rows,ord,ids,wires,field⟩ := h
  exact ⟨size,data,rows,ord,ids,wires,field,R.emittedNumber u size (fun j => (rows j).number)
    (globalCell (scan).toLayout out) ord (fun j => (ids j).1)⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI

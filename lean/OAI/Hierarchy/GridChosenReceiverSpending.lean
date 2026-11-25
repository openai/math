import OAI.Hierarchy.GridChosenReceiverSpendingSetup
import OAI.Hierarchy.GridReceiverGatherSpending
import OAI.Hierarchy.TraceReceiverElectedReplay
import OAI.Hierarchy.TraceReceiverRegisteredGeometry
import OAI.Hierarchy.TraceReceiverJointRoot

namespace OAI
/-! # Charging the chronological receiver and its terminal forest to the selected S43 records -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM HistoryContraction
open Computability.VPVNP.BurstRAM PrivateRAM GridRegisteredSetting TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F] {w pc rr pp size addr fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp size addr fuel axes (w/2)) (l : GridNativeImage.Layout)
local notation "stages" => (D.block.repeat D.passes).length
local notation "locRate" => D.block.localCoefficient*(64*w+1)^3
local notation "teams" => (l.sideMinusOne+1)^(l.dimension+1)*l.copies
local notation "prm" => (GridReceiverDirectory.native D l).parameters

def selectedRoots (h : D.run.plan.History) (t : Fin teams) : List (Fin (D.roots h)) :=
  let unit := D.issuedUnit w l.degree l.stageRate l.rootRate
  let cost := D.costs (GridNativeImage.resources D l) h l.dimension l.sideMinusOne l.bank D.issuedCharges unit
  FactorAllocation.factors w cost (List.finRange (D.roots h)) t

def visitPrice (h : D.run.plan.History) (i : Fin (D.roots h)) : ℕ :=
  D.block.nativeVisitFee stages locRate (D.run.endLevel h 0)*D.rawCharge h i

def rootBill (h : D.run.plan.History) : Fin (D.roots h) → ℕ :=
  D.work h D.issuedCharges (D.issuedUnit w l.degree l.stageRate l.rootRate)

def gatherPrice (h : D.run.plan.History) (i : Fin (D.roots h)) : ℕ :=
  19+1016*(D.issuedTree h i).compile.cells

def rebuild := GridReceiverTickDirectory.clock (64*w)
  (((20*(w+1)+2)^((l.dimension+1)+2))*(prm).roots)

/-- A time bound fixed by the selected terminal ordinals. The writer may spend only
what remains after the native descendant visit and the final row gather are paid. -/
def termAllowance (h : D.run.plan.History) (ids : List (Fin (D.roots h))) : ℕ :=
  rebuild D l+(4226+TraceReceiverTasks.before_clock 0)+∑ i : Fin ids.length,
    (rootBill D l h ids[i]-(visitPrice D h ids[i]+gatherPrice D h ids[i]))

/-- The true tree tariff, stripped only of the legacy map program, also pays when
the intermediate writer memory has not yet been built. -/
theorem visit_gather_le (h : D.run.plan.History) (i : Fin (D.roots h))
    (large : max 64 D.block.stageClockRate ≤ w) (count : stages≤w)
    (stageRate : l.stageRate=fullRate D.block.stageClockRate 0) (rootRate : l.rootRate=TickTerminalRoot.rootFactor)
    (resources : (D.issuedTree h i).resources≤Run.treeFee locRate stages*D.rawCharge h i) :
    visitPrice D h i+gatherPrice D h i≤rootBill D l h i := by
  have positive : 0<D.rawCharge h i := by
    by_contra absent
    have zero : D.rawCharge h i=0 := by omega
    have free := resources
    rw [zero,Nat.mul_zero] at free
    let T:=D.issuedTree h i
    have nodes:=T.nodes_pos
    change T.bits+T.rows+T.nodes+T.footprint.pins≤0 at free
    omega
  have shape := D.issued_shape h
  have q := joint_root D.block (w:=w) (levels:=stages) (ended:=D.run.endLevel h 0) («stages»:=stages)
    (depth:=4+stages) (degree:=l.degree) (D.issuedTree h i) (D.rawCharge h i) (D.issuedPorts h i) 0
    large count shape.1.le (by omega) (shape.2 i) (by unfold Block.localCoefficient;omega)
    positive (D.issued_ports_pay h i) resources (Nat.zero_le _)
  dsimp only at q
  unfold visitPrice gatherPrice rootBill
  rw [stageRate,rootRate,RunData.work_eq_rawCharge]
  dsimp only [RunData.issuedUnit]
  omega

private theorem list_price {a : Type} (L : List a) (f : a → ℕ) :
    (L.map f).sum=∑ i : Fin L.length,f L[i] := by
  calc _ = (List.ofFn (fun i : Fin L.length=>f L[i])).sum :=
              congrArg List.sum (List.ofFn_getElem_eq_map L f).symm
       _ = _ := Fin.sum_ofFn _

variable (z : D.trace) (t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies))

/-- The funded chronological work names the selected roots in exactly the
ordinal order used by the S43 bill, before any receiver RAM executes. -/
theorem elected_work_eq : TraceReceiverElectedCache.rootWork D l z t =
    let ids:=selectedRoots D l z.1 t
    ∑ i : Fin ids.length,visitPrice D z.1 ids[i] := by
  exact list_price (selectedRoots D l z.1 t) (visitPrice D z.1)

set_option maxHeartbeats 1000000 in
/-- The exact chronological compilation and memory-independent terminal allowance,
with the genuine gather spans of the selected compiled trees, fit the same S43 bill. -/
theorem slot_spending (large : max 64 D.block.stageClockRate ≤ w) (count : stages ≤ w)
    (stageRate : l.stageRate=fullRate D.block.stageClockRate 0) (rootRate : l.rootRate=TickTerminalRoot.rootFactor)
    (resources : ∀ i,(D.issuedTree z.1 i).resources≤Run.treeFee locRate stages*D.rawCharge z.1 i) :
    let ids:=selectedRoots D l z.1 t
    let rows:=fun i : Fin ids.length=>(D.issuedTree z.1 ids[i]).compile.cells
    28+16*l.pinWidth+((GridReceiverDirectory.prefixTime D l+(TraceReceiverElectedCache.replay D l z t+termAllowance D l z.1 ids))+
        Gather.fuel (List.ofFn (rootSpan (TickWorkspace.base (TraceAdmission.receiverAge w) 9) rows))) ≤
      setupTime D l+65536*(∑ i : Fin ids.length,rootBill D l z.1 ids[i]) := by
  intro ids rows
  have mature : 10≤w := (by decide : 10≤64).trans ((le_max_left ..).trans large)
  have setup := spending_setup D l mature
  have accounted : (∑ i : Fin ids.length, visitPrice D z.1 ids[i])+
        (∑ i : Fin ids.length, gatherPrice D z.1 ids[i])+
        (∑ i : Fin ids.length, (rootBill D l z.1 ids[i]-(visitPrice D z.1 ids[i]+gatherPrice D z.1 ids[i]))) =
        ∑ i : Fin ids.length, rootBill D l z.1 ids[i] := by
    exact selected_price_sum (fun i : Fin ids.length => rootBill D l z.1 ids[i])
      (fun i => visitPrice D z.1 ids[i]) (fun i => gatherPrice D z.1 ids[i])
      (fun i => visit_gather_le D l z.1 ids[i] large count stageRate rootRate (resources _))
  have gather := gather_fuel (TickWorkspace.base (TraceAdmission.receiverAge w) 9) rows
  change Gather.fuel _ = 6+∑ i : Fin ids.length,gatherPrice D z.1 ids[i] at gather
  rw [gather]
  dsimp only [TraceReceiverElectedCache.replay,termAllowance,rebuild,TraceReceiverDescendantExecution.cost]
  have elected : TraceReceiverElectedCache.rootWork D l z t =
      ∑ i : Fin ids.length, visitPrice D z.1 ids[i] := elected_work_eq D l z t
  rw [elected]
  dsimp only [TraceReceiverDescendantExecution.cost] at setup
  omega

end Hierarchy.GridChosenReceiver
end

end OAI

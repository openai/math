import OAI.Hierarchy.DescentResetHostPadRegisters
import OAI.Hierarchy.DescentPackedMatchChooserFrame

namespace OAI
/-! # Exact predecessor operands and role bytes in the new host rectangle -/
namespace Hierarchy.DescentResetPriorHostPad.Shape
open DescentSIMDLookup DescentOrdinaryHostPad DescentPackedColony ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage.Chooser Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w : ℕ} (s : Shape) (base : ℕ) (src : Fin s.dataRect.pages→Bank)
    (role : Fin s.blocks→Bank) (m : Memory w)
    (safe : ∀j,(src j).Fits w base) (roles : ∀j,(role j).Fits w base) (room : s.endAddress base<2^w)
include safe roles room

/-- Both projections hold in the same final state, including zero for every
new physical host above the preceding archive. -/
theorem issued {a b : ℕ} (data : Fin s.dataRect.pages→Fin s.oldHosts→Fin s.groups→Cell a)
    (values : Fin s.blocks→Fin s.oldHosts→Fin s.groups→Cell b)
    (sources : ∀j, s.oldHosts*chunks s.groups s.operandLanes≤(src j).size ∧ Reads (src j) (data j) s.operandLanes m)
    (tokens : ∀j,s.oldHosts*chunks s.groups s.roleLanes≤(role j).size ∧ Reads (role j) (values j) s.roleLanes m) :
    let out:=(s.phase base src role w).image m
    (∀j,Reads (s.operandBank base j) (extend s.newHosts (data j)) s.operandLanes out) ∧
      ∀j,Reads (s.roleBank base j) (extend s.newHosts (values j)) s.roleLanes out:=by
  intro out
  let mid:=(s.dataRect.phase base src w).image m
  have top:=s.cuts base
  have front:=s.dataRect.any base src m safe (top.2.trans_lt room)
  have carried : ∀j,(role j).Fits w (s.roleStart base):=fun j=>bank_before (roles j) top.1
  have rear:=s.roleRect.any (s.roleStart base) role mid carried room
  constructor
  · intro j
    have got:=s.dataRect.reads base src m safe (top.2.trans_lt room) j (data j) (sources j).1 (sources j).2
    have fit:=s.dataRect.placed base (top.2.trans_lt room) j
    exact reads_before _ _ mid out got (fun i hi=>rear.2 i (.inl hi)) fit.1 fit.2
  · intro j
    have got:=reads_before _ _ m mid (tokens j).2 (fun i hi=>front.2 i (.inl hi)) (roles j) (tokens j).1
    exact s.roleRect.reads (s.roleStart base) role mid carried room j (values j) (tokens j).1 got

end
end Hierarchy.DescentResetPriorHostPad.Shape

end OAI

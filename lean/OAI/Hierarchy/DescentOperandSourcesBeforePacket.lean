import OAI.Hierarchy.DescentResetOperandSetup

namespace OAI
/-! # Executing the retained and signed operand placements before the packet tables -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

set_option maxHeartbeats 1800000 in
/-- The native source passes preserve every address outside the placement interval. -/
theorem sources_run (C : Chart) {w : ℕ} (base : ℕ) (m : Memory w) (s : C.Sources)
    (ready : C.Ready s w base) (good : C.placed base < 2^w) :
    Code.Runs (C.sources base w s) base (C.placed base) m := by
  obtain ⟨a,b,c⟩:=C.before base
  have sr:=c.trans_lt good
  have first:=C.seven.any base s.which s.primary s.old s.matrix s.window s.count s.inverse m
    ready.previous ready.matrix ready.window ready.count ready.inverse ready.lanes ready.blocks sr
  have sec : Code.Runs (C.previous base w s) base (C.placedSigned base) m:=⟨first.1,first.2.2,first.2.1⟩
  have cap {a b : ℕ} (L : Bank) (fit : L.Fits w a) (h : a≤b) : L.Fits w b:=⟨fit.1,fit.2.1,fit.2.2.trans h⟩
  have end_:=C.placement.any C.signedFields (C.placedSigned base) (fun _=>true) s.signed s.count s.inverse
    ((C.previous base w s).image m)
    ready.lanes ready.blocks (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ (a.trans b) (ready.signed i))
    (cap _ ready.count (a.trans b)) (cap _ ready.inverse (a.trans b)) good
  exact Code.combined sec (b:=C.move C.signedFields (C.placedSigned base) w s (fun _=>true) s.signed)
    ⟨end_.1,end_.2.2,end_.2.1⟩ (a.trans b) c

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI

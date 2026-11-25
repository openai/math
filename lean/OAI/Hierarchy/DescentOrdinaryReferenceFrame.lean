import OAI.Hierarchy.DescentOrdinaryReferenceInputs

namespace OAI
/-! # The real compactor remains installed while the six birth pages are materialized -/
namespace Hierarchy.DescentOrdinaryRefsROM.Chart
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (C : DescentOrdinaryRefsROM.Chart)
theorem issued_through {w stop} (m next : Memory w) (rooms : C.Rooms w stop)
    (keep : ∀i<stop,next i=C.output m i) : C.Issued next :=by
  have old:=C.issued m
  have static {a b c} {T : Tables} {g : Cell a→Cell b→Cell c}
      (fitted : Fits T (.lit 0) (.lit 0) a b C.lanes stop w) (printed : Static T g C.lanes (C.output m)) :
      Static T g C.lanes next :=by
    constructor
    · intro i
      have lo : i.val<T.shift.size:=by simpa only [Bank.size,fitted.shiftBits] using i.isLt
      exact (keep _ ((Nat.add_lt_add_left lo _).trans_le fitted.shift.2.2)).trans (printed.1 i)
    · intro i
      have lo : i.val<T.apply.size:=by simpa only [Bank.size,fitted.applyBits] using i.isLt
      exact (keep _ ((Nat.add_lt_add_left lo _).trans_le fitted.apply.2.2)).trans (printed.2 i)
  refine ⟨static (rooms.targets _ _ trivial trivial) old.targets,static (rooms.actors _ _ trivial trivial) old.actors,
    ?_,static (rooms.emit _ _ trivial trivial) old.emit,?_⟩
  · intro j
    have h:=rooms.fields (fun _=>.lit 0) (fun _=>trivial) j
    exact static ⟨trivial,trivial,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩ (old.fields j)
  · intro j i
    have fit:=rooms.dictionary j
    have lo : i.val < (C.dictionary j).size :=by simpa only [Bank.size,fit.2] using i.isLt
    exact (keep _ ((Nat.add_lt_add_left lo _).trans_le fit.1.2.2)).trans (old.dictionary j i)
end
end Hierarchy.DescentOrdinaryRefsROM.Chart

end OAI

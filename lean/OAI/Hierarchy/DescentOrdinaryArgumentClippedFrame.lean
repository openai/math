import OAI.Hierarchy.DescentOrdinaryInletFrames

namespace OAI
/-! # The paid and occupied actor raster survives the full ordinary argument program -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentDatedPriorOperand DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentOrdinaryVenueIngress ProtocolRAM DescentOrdinaryReferenceInputs DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem argument_clipped_frame {w} (floor : ℕ) (A : ArgumentEntry v)
    (match_ : A.Match v floor) (src : OriginSources v) (prepare : NativePhase w)
    (donorFit : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (inlet : A.Room v floor w) (gather : (A.directory v floor match_).refs.Room w (v.vectorStart floor))
    (bounds : ∀j f,(src j f).Fits w (v.origin.outputBase (v.routedStart floor)))
    (cpu : ∀m,prepare.Runs m ∧ ∀i,i<v.routedStart floor ∨ v.origin.grainBase (v.routedStart floor)≤ i → prepare.image m i=m i)
    (m : Memory w) (i : ℕ) (inside : i<A.priorStart v floor) :
    (v.argumentPhaseAfterSigned floor A match_ src prepare donorFit shape fit wide).image m i=
      A.clippedTape v floor m i:=by
  obtain ⟨_,old,role,chip,count⟩:=A.inlet_order v floor
  have f:=A.inlet_frames v floor m inlet
  have after:=v.resolved_any floor (A.directory v floor match_) src prepare (A.chipBank v floor)
    donorFit gather shape fit wide bounds cpu ((A.inlet v floor w).image m)
  have hi₁:=inside.trans_le old
  have hi₂:=hi₁.trans_le role
  have hi₃:=hi₂.trans_le chip
  have edge: i<v.refsStart floor:=match_.atRefs ▸ hi₃.trans_le count
  exact (after.2.1 i (.inl edge)).trans ((f.count i hi₃).trans ((f.chip i hi₂).trans
    ((f.role i hi₁).trans (f.old i inside))))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

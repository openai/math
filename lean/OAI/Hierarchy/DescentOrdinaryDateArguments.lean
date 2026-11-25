import OAI.Hierarchy.DescentOrdinaryArgumentMount
import OAI.Hierarchy.DescentOrdinaryPriorRetile
import OAI.Hierarchy.DescentOrdinaryReferenceInputs
import OAI.Hierarchy.DescentOrdinaryVenueIngressRead
import OAI.Hierarchy.DescentDatedRoutedArguments

namespace OAI
/-! # The same original ordinary tape throughout reference installation, selection and resolution -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentOrdinaryReferenceInputs DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentDatedPriorOperand DescentOperandVectorArena ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)

/-- The predecessor's persistent seven pages retain the physical date's own
packing. Its one public repacking, the population chart and the earlier
roster raster determine every operand fetch address. -/
def dateDirectory (previous : DescentDatedPriorOperand.Layout) (tileBase : ℕ)
    (population : RoleControl.Layout) (venue : DescentOrdinaryVenueIngress.Chart) (venueBase : ℕ)
    (roster : venue.paths=breadth v.reference.degree) (walks : population.walks=breadth v.reference.degree)
    (sites : population.sites=v.vector.lows)
    (oldBlocks : previous.blocks=2^v.reference.k) (oldArgs : previous.operands≤v.vector.operands)
    (newBlocks : v.bornBook.blocks=2^v.reference.k) (newCap : v.bornBook.cap=v.reference.capacity)
    (newArgs : v.bornBook.args=v.vector.operands) :
    Directory (v.refChart floor) v.vector where
  previous:=previous
  tileBase:=tileBase
  priorHosts:=venue.hosts
  priorPitch:=v.vector.lanes*v.vector.radix
  born:=v.bornBook
  birthStart:=v.birthStart floor
  population:=population
  ports:= roster ▸ (venue.shape venueBase).ports
  venues:=venue.fieldBank venueBase
  prevBlocks:=oldBlocks
  prevSlots:=oldArgs
  birthBlocks:=newBlocks
  birthCap:=newCap
  birthArgs:=newArgs
  walks:=walks
  sites:=sites

def mountPhase {w : ℕ} (donor : Bank) (early : donor.Fits w (v.refsStart floor)) (cap : v.vectorStart floor<2^w) : NativePhase w :=
  ⟨v.mountProgram floor donor w,v.mountTime floor donor,v.mountImage floor donor,
    (v.mount_run floor donor (fun _=>0) early cap).2.1⟩

/-- The read expressions and their published route columns come from the
same memory that received this date's six-party argument book. -/
def resolvedPhase {w : ℕ} (R : Directory (v.refChart floor) v.vector) (sources : OriginSources v)
    (preparation : NativePhase w) (donor : Bank) (early : donor.Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2) : NativePhase w :=
  let cap:=(v.vector_before floor).trans_lt ((v.routed_le floor).trans_lt ((v.resolver.floor_le _).trans_lt fit))
  (v.mountPhase floor donor early cap).seq (v.routedArguments floor R.refs sources preparation shape fit wide)

theorem resolved_any {w : ℕ} (R : Directory (v.refChart floor) v.vector) (sources : OriginSources v)
    (preparation : NativePhase w) (donor : Bank) (early : donor.Fits w (v.refsStart floor))
    (gather : R.refs.Room w (v.vectorStart floor)) (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (bounds : ∀j f,(sources j f).Fits w (v.origin.outputBase (v.routedStart floor)))
    (cpu : ∀m,preparation.Runs m ∧ ∀i,i<v.routedStart floor ∨ v.origin.grainBase (v.routedStart floor)≤ i→preparation.image m i=m i)
    (m : Memory w) :
    (v.resolvedPhase floor R sources preparation donor early shape fit wide).Runs m ∧
    (∀i,i<v.refsStart floor ∨ v.endAddress floor≤ i → (v.resolvedPhase floor R sources preparation donor early shape fit wide).image m i=m i) ∧
    (v.refChart floor).Issued ((v.resolvedPhase floor R sources preparation donor early shape fit wide).image m):=by
  have ceiling:=(v.vector_before floor).trans ((v.routed_le floor).trans (v.resolver.floor_le _))
  have cap:=ceiling.trans_lt fit
  have setup:=v.mount_run floor donor m early cap
  let initial:=v.mountImage floor donor m
  let r:=v.routedArguments floor R.refs sources preparation shape fit wide
  have next:=v.routed_run floor R.refs sources preparation gather shape fit wide bounds cpu initial
  obtain ⟨before,after⟩:=v.mount_order floor
  refine ⟨NativePhase.seq_runs _ _ _ setup.1 next.1,?_,?_⟩
  · intro i apart
    exact (next.2 i (apart.imp_left (·.trans_le (before.trans after)))).trans (setup.2.2.1 i
      (apart.imp_right (ceiling.trans ·)))
  · apply (v.refChart floor).issued_through m (r.image initial)
      ((v.refChart floor).rooms (v.ref_end floor).le (after.trans_lt cap))
    intro i h
    exact (next.2 i (.inl (h.trans_le after))).trans
      ((v.bornBook.any donor (v.birthStart floor) ((v.refChart floor).output m)
        ⟨early.1,early.2.1,early.2.2.trans before⟩ cap).2.2 i (.inl h))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

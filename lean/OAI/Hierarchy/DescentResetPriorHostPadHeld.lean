import OAI.Hierarchy.DescentResetHostPadRegisters
import OAI.Hierarchy.DescentDatePortWireRoom
import OAI.Hierarchy.DescentDatedVenueFloor
import OAI.Hierarchy.DescentDatedVenueBelow

namespace OAI
/-! # The original signed stencil, live host census and immutable value survive padding -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentInitialHost DescentColonies DescentPackedColony DescentDatedAddressBook DescentSixParty
open DescentResetPriorHostPad DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {U : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D wire hist w : ℕ}

/-- Transport the original stencil and count across any later allocation preserving earlier addresses. -/
theorem held_below (p : DatePorts) (r : Reached U G q ε S k age z D wire hist) (base finish : ℕ)
    (m next : Memory w) (prior : p.held r base m) (count : p.archive.count.base<base)
    (room : p.WireRoom w base) (block : p.venue.k=k) (cap : p.venue.cap=r.placement.cap)
    (groups : p.venue.groups=S.groupCount age) (grow : base≤finish) (frame : ∀a,a<base→next a=m a) :
    p.held r finish next:=by
  obtain ⟨wide,site,atCount⟩:=prior
  have signed (x : Block k) (j : Fin (2*r.placement.cap)) :
      (p.io.wire x.val j.val).base+p.venue.hosts*chunks (S.groupCount age) p.venue.lanes≤base:=by
    obtain ⟨bank,rows⟩:=room (Fin.cast (congrArg (fun v=>2^v) block.symm) x)
      (Fin.cast (congrArg (fun v=>2*v) cap.symm) j)
    rw [groups] at rows
    exact (Nat.add_le_add_left rows _).trans bank.2.2
  refine ⟨wide,?_,(frame _ count).trans atCount⟩
  have held:=stageVenue_below r wide p.io p.venue.lanes p.venue.paidBits base (r.venueRoster wide)
    m next site signed frame
  exact stageVenue_mono r wide p.io p.venue.lanes p.venue.paidBits base (r.venueRoster wide) next grow held


/-- The preceding output supplies the signed-bank bounds and its census address.
The chronological scan reads from the true preceding host envelope. -/
theorem padded_held (p : DatePorts) (s : Shape) (r : Reached U G q ε S k age z D wire hist) (base : ℕ)
    (src : Fin s.dataRect.pages→Bank) (roles : Fin s.blocks→Bank) (m : Memory w)
    (prior : p.held r base m) (sourceFits : ∀j,(src j).Fits w base)
    (roleFits : ∀j,(roles j).Fits w base) (space : s.endAddress base<2^w)
    (count : p.archive.count.base<base) (room : p.WireRoom w base)
    (block : p.venue.k=k) (cap : p.venue.cap=r.placement.cap) (groups : p.venue.groups=S.groupCount age) :
    (p.padded s base).held r (s.endAddress base) ((s.phase base src roles w).image m) :=by
  have run:=s.any base src roles m sourceFits roleFits space
  exact p.held_below r base (s.endAddress base) m _ prior count room block cap groups
    ((s.cuts base).1.trans (s.cuts base).2) (fun a small => run.2 a (.inl small))

end
end Hierarchy.DescentSixParty.Chronology.DatePorts
end OAI

import OAI.Hierarchy.DescentPhysicalResetDateOutput
import OAI.Hierarchy.DescentDatedVenueBelow
import OAI.Hierarchy.DescentStageVenueWireRoom
import OAI.Hierarchy.DescentVenueRosterDefinition

namespace OAI
/-! # Reading the newly emitted reset venue after the primitive role and metadata passes -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentSIMDLookup DescentColonies
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "venue" => (v).venue
local notation "next" => (venue).next
local notation "fund" => (v).fundedEnd b
local notation "position" => (venue).venueStart fund
local notation "fields" => (venue).sources (FinalInputs.predecessor u) fund
local notation "roleAt" => (v).fullEnd b
variable {F Pin : Type} [Field F] {d : ℕ} {bits : Pin→ℕ} {W : MarkedWorld F d Pin bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {age grain wire hist : ℕ}
  (r : Reached W G q ε S a.successor.venue.next.k age grain a.successor.venue.next.degree wire hist)
  (wide : Fintype.card r.V ≤ a.successor.venue.next.hosts)

theorem date_venue_below (room : z.Room) {m mid dst : Memory w}
    (prefixRun : u.throughOperandDate.Runs m mid) (run : (date z).Runs m dst) :
    ∀j,j<roleAt→dst j=z.venueImage mid j := by
  obtain ⟨out,tailRun,_,_,kept⟩:=z.tail_visible room mid
  have equal : dst=out:=exec_unique _ m dst out run (prefixRun.then tailRun)
  exact fun j hj=>(congrFun equal j).trans (kept j hj)

/-- Both executions refer to the same memory supplied to the funding scans. All
signed sockets, including the padded tail and each true roster row, persist. -/
theorem date_venue (room : z.Room) {m mid dst : Memory w}
    (prefixRun : u.throughOperandDate.Runs m mid) (run : (date z).Runs m dst)
    (groups : S.groupCount age=(next).groups) (cap : r.placement.cap=(next).cap)
    (issued : stageVenue r wide ((next).operands fields position) (next).lanes (next).paidBits
      roleAt (r.venueRoster wide) (z.venueImage mid)) :
    stageVenue r wide ((next).operands fields position) (next).lanes (next).paidBits
      roleAt (r.venueRoster wide) dst := by
  apply stageVenue_below r wide _ _ _ _ _ _ _ issued
  · intro x j
    let ticket := Fin.cast (congrArg (2*·) cap) j
    obtain ⟨inside,rows⟩:=(next).wire_room fields position w x ticket room.successor.return_.roof
    have sizeEq := congrArg (fun count => (next).hosts * chunks count (next).lanes) groups
    exact (Nat.add_le_add_left sizeEq.le _).trans ((Nat.add_le_add_left rows _).trans inside.2.2)
  · exact date_venue_below z room prefixRun run

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

import OAI.Hierarchy.DescentTerminalDatedScanBefore
import OAI.Hierarchy.DescentTerminalObservedRoster

namespace OAI
/-! # The actual actor, signed cable, and peer rows at the last reset's exit -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentPackedColony DescentColonies DescentSIMDLookup DescentSortedRoster DescentActorRaster
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a:PhysicalReset} {floor w:ℕ} {u:a.DateInputs floor w} (z:u.FinalInputs)
local notation "v_" => a.successor
local notation "offset" => a.rebased floor
local notation "venue_" => (v_).venue
local notation "next_" => (venue_).next
local notation "fund" => (v_).fundedEnd offset
local notation "fields" => (venue_).sources (FinalInputs.predecessor u) fund
local notation "loc" => (venue_).venueStart fund
local notation "issued_" => (next_).operands fields loc
local notation "actors_" => (next_).transported fields loc
variable {F Pin:Type} [Field F] {d:ℕ} {sz:Pin→ℕ} {W:MarkedWorld F d Pin sz}
  {G:PoweredGadget F} {q ε:ℝ} {S:DescentCompiler.AtomSchedule} {age grain wire hist:ℕ}
  (r:Reached W G q ε S a.successor.venue.next.k age grain a.successor.venue.next.degree wire hist) (wide:Fintype.card r.V≤a.successor.venue.next.hosts)
local notation "hosts_" => r.vertex.trans (Fin.castLEEmb wide)
local notation "gains" => Venue.actual r.placement (Function.Embedding.refl _) hosts_
local notation "signed_" => Prepare.signed r.placement (r.order.trans Fin.valEmbedding) S r.valid
  (Function.Embedding.refl _) hosts_

/-- The proofs of the packed mask and the individual actor planes refer to the same
venue image. Its date's genuine native tail keeps every bank used by the preflight. -/
theorem returned_terminal_rasters (room:z.Room) {m mid dst:Memory w}
    (start:u.throughOperandDate.Runs m mid) (dateRun:(date z).Runs m dst)
    (groups:S.groupCount age=(next_).groups) (cap:r.placement.cap=(next_).cap)
    (issued:stageVenue r wide issued_ (next_).lanes (next_).paidBits ((v_).fullEnd offset)
      (r.venueRoster wide) (z.venueImage mid))
    (alive:∀x:DescentColonies.Block (next_).k,Reads ((actors_).alive x.val) (gains x) (next_).lanes (z.venueImage mid)):
    (∀x:DescentColonies.Block (next_).k,Reads ((v_).terminalActor offset x.val) (gains x) (next_).lanes dst) ∧
    (∀(x:DescentColonies.Block (next_).k)(j:Fin (2*r.placement.cap)),Reads ((v_).terminalWing offset x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (signed_ x j h g)) (next_).lanes dst) ∧
    (∀i,present (r.terminalRoster wide) (hosts_ i)=(r.placement.near i).map hosts_) ∧
    ∀h j p,indexed (r.terminalRoster wide) h j=some p →
      ((v_).terminalPeer offset).read dst ((h.val*r.placement.degree+j.val:ℕ):Word w)=(p.val:Word w):=by
  have last:=date_venue z r wide room start dateRun groups cap issued
  have hold:=date_venue_below z room start dateRun
  refine ⟨?_,last.2.2.2.1,r.terminal_roster_near wide,?_⟩
  · intro x atRow
    have dim:=(v_).terminal_actor_room offset room.successor.return_.roof x
    have i: (row (next_).hosts (S.groupCount age) (next_).lanes atRow).val<((v_).terminalActor offset x.val).size:=by
      apply (row _ _ _ atRow).isLt.trans_le
      simpa only [groups] using dim.2
    exact (hold _ ((Nat.add_lt_add_left i _).trans_le dim.1)).trans (alive x atRow)
  · exact r.terminal_roster_reads wide issued_ last

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

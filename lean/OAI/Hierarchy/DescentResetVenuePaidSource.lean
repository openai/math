import OAI.Hierarchy.DescentDatedResetVenueRun
import OAI.Hierarchy.DescentStageVenuePaidPages

namespace OAI
/-! # The compact count page at the end of a reset venue -/
namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentColonies DescentSIMDLookup
open DescentPackedZip DescentActorRaster DescentPackedColony DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPackedExchange
open scoped Classical
noncomputable section
variable (v:ResetVenue)(B:Earlier)(base:ℕ)
variable {F P:Type} [Field F] {dim:ℕ}{bits:P→ℕ}{W:MarkedWorld F dim P bits}{G:PoweredGadget F}
  {q ε:ℝ}{S:AtomSchedule}{age z wire hist w used:ℕ}
  (r:Reached W G q ε S v.next.k age z v.next.degree wire hist)(wide:Fintype.card r.V≤v.next.hosts)
local notation "A" => r.placement
local notation "names" => r.vertex.trans (Fin.castLEEmb wide)
local notation "fields" => v.sources B base
local notation "φ" => DescentVenueQuantityPlanes.phase v.dense (v.paidLayout B base) w
local notation "α" => DescentVenueQuantityPlanes.phase v.actorDims (v.actorLayout B base) w
local notation "π" => DescentCompactVenuePeers.phase B.ranks (v.peerStart base) v.rawHosts v.dense.hosts w B.tag

theorem paid_source_after (m:Memory w)(f:v.RunRoom B base used w)
    (groups:S.groupCount age=v.next.groups)
    (paidEarly:∀x:DescentColonies.Block v.next.k,((fields).paid x.val).base+((fields).paid x.val).size≤v.actorStart base)
    (paid:StageVenueTail.paidCounts fields r wide v.next.paidBits v.next.paidLanes ((φ).image m)) :
    ∀x:DescentColonies.Block v.next.k,Source (.lookup ((fields).paid x.val) .row)
      (fun h g=>Census.count (A) (Equiv.refl _) names v.next.paidBits h g x)
      v.next.paidLanes ((v.phase B base w).image m):=by
  let pm:=(φ).image m
  let am:=(α).image pm
  have actorFrame:=(DescentVenueQuantityPlanes.any v.actorDims (v.actorLayout B base) pm f.actors).2
  have peerFrame:=(DescentCompactVenuePeers.any B.ranks (v.peerStart base) v.rawHosts v.dense.hosts w B.tag
    am f.roster f.peerEnd).2
  have early:StageVenueTail.paidCounts fields r wide v.next.paidBits v.next.paidLanes ((π).image am):=by
    intro x p
    have fits: v.next.hosts*chunks (S.groupCount age) v.next.paidLanes≤((fields).paid x.val).size :=by
      rw [groups];exact (f.return_.paid x).2
    have idx:=(row _ _ _ p).isLt.trans_le fits
    have lo:=(Nat.add_lt_add_left idx ((fields).paid x.val).base).trans_le (paidEarly x)
    exact (peerFrame _ (.inl (lo.trans_le (v.steps base).2.1))).trans
      ((actorFrame _ (.inl lo)).trans (paid x p))
  have kept:=v.next.paid_counts_after fields r wide groups (v.venueStart base) ((π).image am) f.return_ early
  intro x
  exact source_column _ (v.venueStart base) (f.return_.paid x).1 _ _
    (by rw [groups];exact (f.return_.paid x).2) (kept x)

end
end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI

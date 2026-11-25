import OAI.Hierarchy.DescentDatedResetVenueRun
import OAI.Hierarchy.DescentStageVenuePeers

namespace OAI
/-! # Preserving the actual reset receipts through the complete successor program -/
namespace Hierarchy.DescentDatedAddressBook.ResetVenue
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentColonies DescentSIMDLookup
open DescentActorRaster DescentPackedColony DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPackedExchange
open scoped Classical Fin.CommRing
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

/-- Each true numeric shelf is authenticated at the instant its producer writes it. -/
theorem returned (m:Memory w)(f:v.RunRoom B base used w)
    (groups:S.groupCount age=v.next.groups)(cap:(A).cap=v.next.cap)
    (alivePos:0<v.next.aliveLanes)(signedPos:0<v.next.signedLanes)(paidPos:0<v.next.paidLanes)
    (paidEarly:∀x:DescentColonies.Block v.next.k,((fields).paid x.val).base+((fields).paid x.val).size≤v.actorStart base)
    (actorEarly:∀x:DescentColonies.Block v.next.k,((fields).alive x.val).base+((fields).alive x.val).size≤v.peerStart base)
    (cableEarly:∀(x:DescentColonies.Block v.next.k)(j:Fin (2*(A).cap)),(B.signed x.val j.val).base+(B.signed x.val j.val).size≤v.denseStart base)
    (paid:∀x:DescentColonies.Block v.next.k,Reads ((fields).paid x.val) (fun h g=>Census.count (A) (Equiv.refl _) names v.next.paidBits h g x)
      v.next.paidLanes ((φ).image m))
    (actor:∀x:DescentColonies.Block v.next.k,Reads ((fields).alive x.val) (Venue.actual (A) (Function.Embedding.refl _) names x)
      v.next.aliveLanes ((α).image ((φ).image m)))
    (neighbors:∀(h:Fin v.next.hosts)(j:Fin v.next.degree),(π).image ((α).image ((φ).image m)) ((fields).roster.base+(h.val*v.next.degree+j.val))=
      (DescentPackedColony.target (r.venueRoster wide h j):Word w))
    (hub:∀h:Fin v.next.hosts,(π).image ((α).image ((φ).image m)) ((fields).hub.base+h.val)=((Census.hub (A) names h).val:Word w))
    (signed:∀(x:DescentColonies.Block v.next.k)(j:Fin (2*(A).cap)),Reads (B.signed x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (Prepare.signed (A) (r.order.trans Fin.valEmbedding)
        S r.valid (Function.Embedding.refl _) names x j h g)) v.next.signedLanes m):
    stageVenue r wide (v.next.operands fields (v.venueStart base)) v.next.lanes v.next.paidBits
      (v.endAddress base) (r.venueRoster wide) ((v.phase B base w).image m):=by
  have f₀:=(DescentVenueQuantityPlanes.any v.dense (v.paidLayout B base) m f.paid).2
  have f₁:=(DescentVenueQuantityPlanes.any v.actorDims (v.actorLayout B base) ((φ).image m) f.actors).2
  have f₂:=(DescentCompactVenuePeers.any B.ranks (v.peerStart base) v.rawHosts v.dense.hosts w B.tag
    ((α).image ((φ).image m)) f.roster f.peerEnd).2
  have phases:=v.steps base
  apply v.next.phase_source fields r wide (v.venueStart base) _ groups cap alivePos signedPos paidPos
    (r.venueRoster wide) f.return_ neighbors hub
  · intro x p
    have size:=(f.return_.alive x).2
    have small:(row v.next.hosts (S.groupCount age) v.next.aliveLanes p).val<((fields).alive x.val).size:=
      (row v.next.hosts (S.groupCount age) v.next.aliveLanes p).isLt.trans_le (by simpa only [groups] using size)
    exact (f₂ _ (.inl ((Nat.add_lt_add_left small _).trans_le (actorEarly x)))).trans (actor x p)
  · intro x p
    have size:=(f.return_.paid x).2
    have small:(row v.next.hosts (S.groupCount age) v.next.paidLanes p).val<((fields).paid x.val).size:=
      (row v.next.hosts (S.groupCount age) v.next.paidLanes p).isLt.trans_le (by simpa only [groups] using size)
    have low:=(Nat.add_lt_add_left small _).trans_le (paidEarly x)
    exact (f₂ _ (.inl (low.trans_le phases.2.1))).trans ((f₁ _ (.inl low)).trans (paid x p))
  · intro x j p
    have s:=(f.return_.signed x (Fin.cast (congrArg (2*·) cap) j)).2
    have small:(row v.next.hosts (S.groupCount age) v.next.signedLanes p).val<(B.signed x.val j.val).size:=
      (row v.next.hosts (S.groupCount age) v.next.signedLanes p).isLt.trans_le (by simpa only [groups, sources, Fin.val_cast] using s)
    have low:=(Nat.add_lt_add_left small _).trans_le (cableEarly x j)
    exact (f₂ _ (.inl (low.trans_le (phases.1.trans phases.2.1)))).trans
      ((f₁ _ (.inl (low.trans_le phases.1))).trans ((f₀ _ (.inl low)).trans (signed x j p)))

end
end Hierarchy.DescentDatedAddressBook.ResetVenue

end OAI

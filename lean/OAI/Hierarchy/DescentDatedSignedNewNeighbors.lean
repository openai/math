import OAI.Hierarchy.DescentDatedSignedAfterMark
import OAI.Hierarchy.DescentOrdinaryVenueProof
import OAI.Hierarchy.DescentDatedVenueBelow

namespace OAI
/-! # The normalized successor neighbor directory at the signed writer's input -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentColonies
open DescentGroupPeerOrder DescentDyadicSpan DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)
local notation "ph" => v.withIssuedSigned
local notation "s₀" => (ph).signed
local notation "H" => v.area.H
local notation "D" => v.area.D
local notation "R" => v.venue.hosts
local notation "E" => v.venue.degree
variable (floor:ℕ) (input:Stage.Dated.Operands) (count parts adj:Bank) {w:ℕ}
local notation "base" => (ph).materialEnd floor
local notation "first" => (ph).donorEnd floor
local notation "src₀" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "geo" => PriorHeader.reverseRank H (s₀).groups (s₀).lanes (s₀).degree first
local notation "I₀" => (ph).signedInput floor v.issuedSignedChart
local notation "peerPage" => DescentOrdinaryPeerRows.peers base H D R E

/-- Both real and padding hosts use the same earlier geometric directory, even when
a real site has no incident positive cable. The marking phase retains every peer row. -/
theorem signed_neighbors (m:Memory w) {pitch precision lower:ℕ}
    (oldFit:Fintype.card v.prior.V≤H) (newFit:Fintype.card v.target.V≤R)
    (income:stageVenue v.prior oldFit input pitch precision lower (v.prior.venueRoster oldFit) m)
    (wires:∀(x:Block v.k)(j:Fin (2*v.prior.placement.cap)),
      (input.wire x.val j.val).base+H*chunks (v.schedule.groupCount v.age) pitch≤lower)
    (countRead:m count.base=(Fintype.card v.prior.V:Word w)) (countLow:count.base<lower) (place:lower≤first)
    (pre:PriorHeader.Room adj H (s₀).groups (s₀).lanes (s₀).degree first w)
    (mat:(ph).MaterialRoom ((ph).materialStart floor) parts geo w)
    (room:DescentOrdinaryVenueReturn.Room src₀ base H D R E w)
    (mark:(ph).MarkRoom floor input w)
    (degree:D=v.degree) (nextDegree:E=v.nextDegree) :
    let host:=v.target.vertex.trans (Fin.castLEEmb newFit)
    ∀(h:Fin R)(j:Fin v.target.placement.degree),
      (v.signedPredecessor floor input count parts adj w).image m
        ((I₀).newNeighbors.base+(h.val*v.target.placement.degree+j.val))=
      (number (Stage.hostRotor host (hostRoster v.target.placement (host.trans Fin.valEmbedding)) h j):Word w):=by
  intro host h j
  let prior:=((ph).beforeSignedMaterial floor parts adj w).image m
  have frame (a:ℕ) (ha:a<lower):prior a=m a:=
    ((ph).before_signed_any floor parts adj pre mat m).2 a (.inl (ha.trans_le place))
  have measured:=stageVenue_below v.prior oldFit input pitch precision lower (v.prior.venueRoster oldFit)
    m prior income wires frame
  have cutoff:lower≤base:=place.trans ((ph).signed_stage_paid floor).1
  have rooms:=room
  rw [degree,nextDegree] at rooms
  have header:=v.ticket.return_header oldFit newFit input count base prior measured cutoff
    ((frame _ countLow).trans countRead) rooms
  let index:Fin v.nextDegree:=Fin.cast v.target.branch j
  have branch:v.target.placement.degree=E:=v.target.branch.trans nextDegree.symm
  let col:Fin E:=Fin.cast branch j
  have offset:h.val*E+col.val<R*E:=by
    simpa [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (h,col)).isLt
  have live:(peerPage).base+(h.val*E+col.val)<(ph).peerTail floor:=by
    have spanBound:=offset.trans_le (span_ge (R*E))
    change (peerPage).base+(h.val*E+col.val)<DescentOrdinaryVenueReturn.roof base H D R E
    unfold DescentOrdinaryVenueReturn.roof DescentOrdinaryVenueReturn.hubs
      DescentOrdinaryVenueReturn.bookStart DescentOrdinaryPeerCount.roof
      DescentOrdinaryPeerRows.endAddress DescentOrdinaryPeerChart.top DescentOrdinaryPeerRows.peers
    dsimp only
    omega
  have read: (DescentOrdinaryVenueReturn.phase src₀ base v.k H D R E w).image prior
      ((peerPage).base+(h.val*E+col.val))=
      (number (Stage.hostRotor host (hostRoster v.target.placement (host.trans Fin.valEmbedding)) h j):Word w):=by
    have sameOrder : (v.target.vertex.trans (Fin.castLEEmb newFit)).trans Fin.valEmbedding =
        v.target.vertex.trans Fin.valEmbedding := by ext a; rfl
    simpa only [degree,nextDegree,Reached.venueRoster,DescentPackedColony.target,number,index,col,Fin.val_cast,
      Fin.cast_cast,Fin.cast_refl,host,sameOrder,id_eq] using header.2.1 h index
  have stable:=(v.signed_predecessor_frames floor input count parts adj m mat room mark).2.2 _ live
  have addr:h.val*v.target.placement.degree+j.val=h.val*E+col.val:=
    congrArg (fun d=>h.val*d+j.val) branch
  rw [addr]
  exact stable.trans read

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

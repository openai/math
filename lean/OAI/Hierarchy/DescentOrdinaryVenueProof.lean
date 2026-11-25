import OAI.Hierarchy.DescentOrdinaryVenueMachine
import OAI.Hierarchy.DescentStageVenuePeers

namespace OAI
/-! # True old and new measured directories in the same ordinary handover -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentPackedExchange DescentHostDegree DescentOrdinaryVenueReturn DescentDyadicSpan DescentCompiler DescentGroupPeerOrder DescentHostDirectory
open DescentSIMDLookup DescentPackedColony DescentPacking.PackedMatch.Local.Stage Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {dim k:ℕ} {bits:P→ℕ}{W:MarkedWorld F dim P bits}
  {G:PoweredGadget F}{q ε u:ℝ}{S:AtomSchedule}{age z D wire hist z₁ E H R w:ℕ}
  {src:Reached W G q ε S k age z D wire hist}{he:0≤ε}{T:StageInput W G u ε}{choice:(T.result he).Choice}
  {norm:Normalize ((T.result he).state choice)}{dst:Reached norm.result G q ε S k (age+1) z₁ E wire hist}
  (link:OrdinaryLink src he T choice norm dst)
  (oldFit:Fintype.card src.V≤H)(newFit:Fintype.card dst.V≤R)
  (I:Dated.Operands)(count:Bank)(base:ℕ)
local notation "banks" => (⟨count,I.roster,I.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "start" => bookStart base H D R E
local notation "out" => (hubs base H D R E).base
local notation "sh" => «public» k D
local notation "before" => DescentOrdinaryPeerCount.program w base H D R E count I.roster sh
local notation "full" => phase banks base k H D R E w
local notation "peers" => DescentOrdinaryPeerRows.peers base H D R E
local notation "end_" => roof base H D R E
local notation "fields" => ordinaryHubRow k (shapeSlots D) (gain D)

include link in
theorem OrdinaryLink.return_header {M precision floor:ℕ}(m:Memory w)
    (income:stageVenue src oldFit I M precision floor (src.venueRoster oldFit) m) (prior:floor≤base)
    (measured:m count.base=(Fintype.card src.V:Word w))(fit:Room banks base H D R E w):
    (full).Runs m ∧
    (∀h j,(full).image m ((peers).base+(h.val*E+j.val))=(DescentPackedColony.target (dst.venueRoster newFit h j):Word w)) ∧
    (∀h,(full).image m (out+h.val)=((Census.hub dst.placement (dst.vertex.trans (Fin.castLEEmb newFit)) h).val:Word w)) ∧
    (full).image m (DescentOrdinaryPeerCount.newCount base H D R E).base=(Fintype.card dst.V:Word w) ∧
    ∀x,x<base ∨ end_≤x→(full).image m x=m x:=by
  have all:=any banks base k H D R E w m fit
  obtain ⟨high,startAt,peerSpace,tableEnd,ownersFit,maskFit,oldBitFit,hubRoom⟩:=parts banks base H D R E w fit
  have mk:=link.venue_peers base I count m oldFit newFit income prior fit.count measured peerSpace
  let routed := DescentOrdinaryPeerCount.program w base H src.placement.degree R dst.placement.degree
    count I.roster («public» k src.placement.degree)
  have samePhase : routed = before := by
    dsimp only [routed]
    rw [src.branch, dst.branch]
  have current (x:ℕ) (bound:x<base):(before).image m x=m x:=by
    rw [← samePhase]
    exact mk.2.1 x (Or.inl bound)
  have peerRead (h:Fin R)(j:Fin E):(before).image m ((peers).base+(h.val*E+j.val))=(DescentPackedColony.target (dst.venueRoster newFit h j):Word w):=by
    rw [← samePhase, ← Nat.add_assoc]
    exact mk.2.2.2 h j
  have newCount:(before).image m (DescentOrdinaryPeerCount.newCount base H D R E).base=(Fintype.card dst.V:Word w):=by
    rw [← samePhase]
    exact mk.2.2.1
  let fixed:=DescentStaticWordColumn.image start (word k D R) ((before).image m) (2*span R)
  have two (x:ℕ) (bound:x<start):(full).image m x=(before).image m x:=
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ fixed x (.inl (bound.trans_le ((Nat.le_add_right ..).trans_eq tableEnd)))).trans
      (DescentStaticWordColumn.frame _ _ _ _ x (.inl bound))
  have priorHub (j:Fin H):fixed (I.hubs.base+j.val)=((Census.hub src.placement (src.vertex.trans (Fin.castLEEmb oldFit)) j).val:Word w):=by
    have low : I.hubs.base+j.val<base:=
      (Nat.add_lt_add_left (j.isLt.trans_le income.2.2.2.2.2.1) _).trans_le fit.hub.2.2
    exact (DescentStaticWordColumn.frame _ _ _ _ _ (.inl (low.trans_le startAt))).trans ((current _ low).trans (income.2.2.2.2.2.2.1 j))
  have layout (j:Fin R):
      fixed ((owners base H D R E).base+j.val)=((fields j.val).1:Word w) ∧
      fixed ((masks base H D R E).base+j.val)=((fields j.val).2.toNat:Word w):=by
    have size:=j.isLt.trans_le (span_ge _)
    constructor
    · exact (DescentStaticWordColumn.read start (2*span R) (word k D R) _ (by omega:j.val<2*span R)).trans (by simp [word,size])
    · change fixed (start+span R+j.val)=_
      dsimp only [fixed]
      rw [Nat.add_assoc,DescentStaticWordColumn.read _ _ _ _ (by omega:span R+j.val<2*span R)]
      simp [word]
  have hubRead:=link.issued_hubs oldFit newFit (owners base H D R E) I.hubs (masks base H D R E) out fixed
    ownersFit oldBitFit maskFit (span_ge _) (span_ge _) income.2.2.2.2.2.1 hubRoom priorHub
    (fun j=>by simpa only [src.branch,shapeSlots,gain] using layout j)
  refine ⟨all.1,?_,hubRead.2.1,?_,all.2⟩
  · intro h j
    apply (two _ ?_).trans (peerRead h j)
    have row : h.val*E+j.val<R*E:=by have:= (finProdFinEquiv (h,j)).isLt;simpa [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using this
    have take:=row.trans_le (span_ge _)
    change _<DescentOrdinaryPeerRows.endAddress base H D R E+1
    change (peers).base + (h.val * E + j.val) < (peers).base + span (R*E) + 1
    omega
  · exact (two _ (Nat.lt_succ_self _)).trans newCount

end
end Hierarchy.DescentSixParty.Chronology

end OAI

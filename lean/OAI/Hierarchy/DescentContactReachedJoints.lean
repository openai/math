import OAI.Hierarchy.DescentContactJointGeometry
import OAI.Hierarchy.DescentResetContactRightHalo
import OAI.Hierarchy.DescentContactPreROMRead
import OAI.Hierarchy.DescentContactMarkerShape
import OAI.Hierarchy.DescentContactCoordinateJoint
import OAI.Hierarchy.DescentResetPublicDonorRead

namespace OAI
/-! # Authentic old signed representatives of both new endpoint coordinates -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentResetLocalRoster DescentDenseHostOrder DescentSIMDLookup
open DescentContactDonorSelection DescentContactReceiver DescentReservedSocketPanel DescentReservedPeerMarker DescentFirstContactPayload
open DescentContactCoordinateJoint DescentResetParentCodec
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "A" => input.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "rad" => 2^(Nat.clog 2 ((A).degree+2))
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "N" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(A).cap)
local notation "site" s:arg c:arg => (if s then (blocks B).dst (contactParent B c) else (blocks B).src (contactParent B c))
local notation "center" s:arg c:arg => ((Z).rootVertex T ((R).owner s c),(Z).rootBlock T ((R).owner s c))

def endpointProbe (s : Bool) (c : (R).Contact) : ContactProbe B:=
  (s,(Z).rootTicket T ((R).owner s c),⟨_,(Z).contactSlotWord_lt T s c⟩)

theorem query_probe (s : Bool) (c : (R).Contact) :
    donor_query B (probeId B (endpointProbe B s c))=(s,(Z).senderJoint T s c):=by
  let slot : Fin (2^(Z).n + 2^Ht) := ⟨(Z).contactSlotWord T s c,(Z).contactSlotWord_lt T s c⟩
  let root := rootId r (2^(Z).n) ((Z).rootTicket T ((R).owner s c))
  let row := finProdFinEquiv (root,slot)
  let pair := (finTwoEquiv.symm s,row)
  change (finTwoEquiv (finProdFinEquiv.symm (finProdFinEquiv pair)).1,
    (finProdFinEquiv.symm (finProdFinEquiv pair)).2.val + 1) = _
  rw [Equiv.symm_apply_apply]
  apply Prod.ext
  · exact finTwoEquiv.apply_symm_apply _
  · change (finProdFinEquiv (root,slot)).val+1 = root.val*(2^(Z).n+2^Ht)+slot.val+1
    rw [finProdFinEquiv_apply_val]
    ring

theorem donor_query_injective : Function.Injective (donor_query B):=by
  intro x y eqn
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · exact finTwoEquiv.injective (congrArg Prod.fst eqn)
  · apply Fin.ext
    exact Nat.add_right_cancel (congrArg Prod.snd eqn)

private theorem mark_at_shape {n ports : ℕ} (board : NonlinearExpanders.Graph n ports)
    (depth ht : ℕ) (side : Bool) (ticket : Root depth (2^n)) (socket : Fin (2^n+2^ht))
    (sourceShape here there own remote serial span localDepth peerDepth port : ℕ)
    (decoded : peer depth (2^n) ht ticket socket.val own remote serial span = remote)
    (address : DescentResetPublicParentWord.send ⟨0,depth,2^n,0,0,0,0⟩ ht ticket socket = own)
    (localShape : DescentResetPublicParentWord.outputShape board depth ht side own localDepth = here+1)
    (peerShape : DescentResetPublicParentWord.outputShape board depth ht (!side) remote peerDepth = there+1)
    (positive : remote ≠ 0) :
    mark board depth ht side ticket socket sourceShape own remote serial span localDepth peerDepth port =
      if here=sourceShape then 1+port*(DescentDenseHostOrder.roster board depth ht).card+there else 0 := by
  by_cases same : here=sourceShape <;>
    simp [mark,decoded,address,localShape,peerShape,positive,same]; omega

set_option maxHeartbeats 1000000 in
/-- All real old grains of the requested socket have the same opposite shape.
Another raw shape over that same old host has no marker, even if the socket has nonzero mass. -/
theorem own_socket_marker (u : Host) (s : Bool) (j : Fin N) (e : (old).graph.Edge)
    (present : originalDonor B u s j=some e) :
    let c:=(R).contact e
    contactSheet B u (probeId B (endpointProbe B s c)) (finProdFinEquiv (finTwoEquiv.symm s,j))=
      if relativeShape B (site s c)=relativeShape B u then
        1+(contactOldPort B s e).val*shelf+relativeShape B (site (!s) c) else 0:=by
  intro c
  refine (contactSheet_read B u (endpointProbe B s c) j).trans ?_
  change (originalDonor B u s j).elim 0 _=_
  rw [present]
  let digit:=contactTicketDigit B c
  let span:=contactPairSpan B c
  have key : peer r (2^(Z).n) Ht ((Z).rootTicket T ((R).owner s c)) ((Z).contactSlotWord T s c)
      ((Z).senderJoint T s c) ((Z).senderJoint T (!s) c) digit span=(Z).senderJoint T (!s) c:=by
    cases hc : c with
    | inl t=>simpa only [digit,span,hc,contactTicketDigit,contactPairSpan] using good_sibling (Z) T s t t.2
    | inr t=>simpa only [digit,span,hc,contactTicketDigit,contactPairSpan] using fallback (Z) T s t 0 0
  have own : DescentResetPublicParentWord.send ⟨0,r,2^(Z).n,0,0,0,0⟩ Ht (endpointProbe B s c).2.1 (endpointProbe B s c).2.2=
      (Z).senderJoint T s c:=rfl
  change mark _ _ _ s (endpointProbe B s c).2.1 (endpointProbe B s c).2.2 (relativeShape B u)
    ((Z).senderJoint T s c) ((Z).senderJoint T (!s) c) digit span ((Z).contactDepth s c)
    ((Z).contactDepth (!s) c) (contactOldPort B s e).val=_
  have actualPeer : peer r (2^(Z).n) Ht (endpointProbe B s c).2.1 (endpointProbe B s c).2.2.val
      ((Z).senderJoint T s c) ((Z).senderJoint T (!s) c) digit span = (Z).senderJoint T (!s) c := key
  exact mark_at_shape (Z).graph r Ht s (endpointProbe B s c).2.1 (endpointProbe B s c).2.2
    (relativeShape B u) (relativeShape B (site s c)) (relativeShape B (site (!s) c))
    ((Z).senderJoint T s c) ((Z).senderJoint T (!s) c) digit span
    ((Z).contactDepth s c) ((Z).contactDepth (!s) c) (contactOldPort B s e).val actualPeer own
    (joint_endpoint B s c) (joint_endpoint B (!s) c) (sender_not_zero B (!s) c)

/-- The old signed-label fold is defined even away from the true socket shape.
A positive original count supplies a real representative and the label rejects every other contact. -/
theorem pick_socket {a b : ℕ} (u : Host) (s : Bool) (c : (R).Contact) (root : receiverRoot B u=center s c)
    (represented : ∃e : (old).graph.Edge,(R).contact e=c) (own : Fin N→Cell a) (cargo : Fin N→Cell b)
    (v : Cell b) (label : ∀j,(own j).val=(originalDonor B u s j).elim 0 (fun e=>(Z).senderJoint T s ((R).contact e)))
    (sent : ∀j e,originalDonor B u s j=some e→(R).contact e=c→cargo j=v) :
    visits ((Z).senderJoint T s c) own cargo=v:=by
  have hit (j : Fin N) (yes : (own j).val=(Z).senderJoint T s c) : cargo j=v:=by
    cases row : originalDonor B u s j with
    | none=>
      have empty : (own j).val=0:=by rw [label,row];rfl
      exact (sender_not_zero B s c (yes.symm.trans empty)).elim
    | some e=>
      have here:=contact_old_slot_location B u s (finProdFinEquiv.symm j) e row
      have same:=here.symm.trans root
      exact sent j e row (contact_sender_word_unique B s (congrArg Prod.fst same) (congrArg Prod.snd same)
        (by simpa [label,row] using yes))
  by_cases zero : v=0
  · rw [zero]
    apply (first_eq_zero _).2
    intro j
    by_cases eqn : (own j).val=(Z).senderJoint T s c
    · simp [keep,eqn,sender_not_zero B,hit j eqn,zero]
    · simp [keep,eqn]
  · obtain ⟨e,who⟩:=represented
    obtain ⟨j,here⟩:=originalDonor_exists B u s c root e (congrArg ((R).owner s) who)
    apply found _ _ _ _ (sender_not_zero B s c) _ hit
    exact ⟨j,by simp [label,here,who],by rwa [sent j e here who]⟩

/-- Exact one-based halo of either authenticated contact end lies strictly below the code radix. -/
theorem endpoint_mem (u : Host) (s : Bool) (e : (old).graph.Edge) (j : Fin N) (at_ : originalDonor B u s j=some e)
    (end_ : Bool) : (Z).rootVertex T ((R).owner end_ ((R).contact e))∈originDomain B u:=by
  have same:=congrArg Prod.fst (contact_old_slot_location B u s (finProdFinEquiv.symm j) e at_)
  by_cases eqn:end_=s
  · subst end_;exact Finset.mem_insert.mpr (.inl same.symm)
  · have rev : end_= !s:=by cases s <;>cases end_ <;>simp_all
    rw [rev]
    apply Finset.mem_insert.mpr
    right
    rw [same]
    simp only [contact_owner_host B]
    apply (origin_neighbor B _ _).mpr
    simp only [Equiv.symm_apply_apply]
    cases s
    · obtain ⟨v,mem,there⟩:=Finset.mem_map.mp ((A).peers e.1).1
      exact (congrArg Prod.snd there) ▸ mem
    · obtain ⟨v,mem,there⟩:=Finset.mem_map.mp ((A).peers e.1).2
      exact (congrArg Prod.snd there) ▸ mem

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

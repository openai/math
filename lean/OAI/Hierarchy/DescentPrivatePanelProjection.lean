import OAI.Hierarchy.DescentPrivateReachedMask
import OAI.Hierarchy.DescentPrivateMaskPeriod
import OAI.Hierarchy.DescentResetPeerRootOrigins
import OAI.Hierarchy.DescentResetOriginalFees
import OAI.Hierarchy.DescentResetPeerCorrectionRoom
import OAI.Hierarchy.DescentResetPeerActorChart

namespace OAI
/-! # The physically mounted private panel, the original grain count and both pointed-to shapes -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentParallelBase
open DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentGroupPeerOrder
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "D₀" => input.placement.degree
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

variable {H field keyBits bits count : ℕ} (pad : Fintype.card input.V ≤ H)
local notation "padded" => (vertex).trans (Fin.castLEEmb pad)
local notation "named" => (Z).rawHostRank T padded
local notation "coords" => (Z).hostFields T padded
local notation "pitch" => H*shelf


open DescentResetLocalRoster DescentPackedPrivateMenu DescentResetPeerUnionRAM
variable (prior : PriorPeerWords B H field keyBits)
local notation "groups₁" => S.groupCount (i+1)
local notation "host₁" => Stage.Host (Fin groups₁) B.next.V k
local notation "orig" => (fun (u:host₁)=>vertex (receiverRoot B u).1)

def privateProjection (oldBatch batch metaBits : ℕ) : DescentPrivateMaskDeck.Shape :=
  ⟨H,shelf,groups₁,2^k,oldBatch,batch,capacity,field,metaBits,r,2^(Z).n⟩

theorem private_lane_size : groups₁*2^k=J := by
  simpa only [Fintype.card_fin,Fintype.card_prod] using
    (Fintype.card_congr (S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth)).symm

theorem private_lane_at (u : host₁) :
    (finProdFinEquiv (u.1.1,u.2)).cast (private_lane_size B)=peerLane B u:=by rfl

private theorem root_at (u : host₁) :
    DescentContactProbePitch.owner (named u.1.2)=(orig u).castLE pad := by
  change (finProdFinEquiv.symm (finProdFinEquiv ((Z).hostFields T padded u.1.2))).1=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem private_row_numbers (oldBatch batch metaBits : ℕ) (u : host₁) (side : Bool)
    (t : (Z).RootTicket T) (slot : Fin capacity) (fld : Fin 3) :
    let A:=privateProjection (H:=H) (field:=field) B oldBatch batch metaBits
    let raw:=priorPrivate B pad prior (orig u) (receiverRoot B u).2 side t slot
    (A.scalar slot fld (prior.privatePages side t (DescentContactProbePitch.owner (named u.1.2))
      ((finProdFinEquiv (u.1.1,u.2)).cast (private_lane_size B)))).val=
       (if raw 0=1 then raw ⟨fld.val+1,by omega⟩ else 0)%2^metaBits :=by
  dsimp only
  rw [root_at B pad,private_lane_at B u]
  let raw:=priorPrivate B pad prior (orig u) (receiverRoot B u).2 side t slot
  let index : Fin 5 := ⟨fld.val+1, by omega⟩
  change (if raw 0=1 then (raw index : Cell metaBits) else 0).val =
    (if raw 0=1 then raw index else 0) % 2^metaBits
  by_cases present : raw 0=1 <;> simp only [present, ↓reduceIte] <;> rfl

theorem private_count_room (p : PrivateOccurrence B) : (blocks B).count (privateWire B p)≤B.next.placement.cap :=by
  let e:=privateWire B p
  by_cases positive : 0<(blocks B).count e
  · let u:=(blocks B).src e
    let l : Local (blocks B) u:=⟨e,positive,Or.inl rfl⟩
    exact (Finset.single_le_sum (f:=fun a : Local (blocks B) u=>(blocks B).count a.val)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ l)).trans (local_count_le B u)
  · exact (Nat.le_of_not_gt positive).trans (Nat.zero_le _)

/-- Natural values of all three representable output digits. In an empty root or
oversized wire slot all three are zero. At a live root the native width fits because
each grain is incident to its true source and is counted by the successor capacity. -/
theorem private_fields_fit (unit : 0<(Z).unit)
    (panels : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel height count)
    (issued : PeerOrigins B pad prior unit panels) (u : host₁) (side : Bool)
    (t : (Z).RootTicket T) (slot : Fin capacity) (metaBits : ℕ)
    (shapeFit : shelf≤2^metaBits) (widthFit : B.next.placement.cap<2^metaBits) (j : Fin 3) :
    let raw:=priorPrivate B pad prior (orig u) (receiverRoot B u).2 side t slot
    (if raw 0=1 then raw ⟨j.val+1,by omega⟩ else 0)<2^metaBits :=by
  let v:=orig u
  let g:=(receiverRoot B u).2
  let raw:=priorPrivate B pad prior v g side t slot
  change (if raw 0=1 then raw _ else 0)<_
  split
  next present=>
    obtain ⟨p,atSlot⟩:=(private_raw_presence B unit side t v g slot (panels side) raw
      (issued.numbers v g side t slot) (issued.installed v g side t slot)).1.1 present
    obtain ⟨_,source,target,amount,_⟩:=issued_relative B p raw (issued.installed _ _ _ _ _ p atSlot) unit
    have shape (a : host₁) : relativeShape B a<2^metaBits:=((coords a.1.2).2.isLt).trans_le shapeFit
    fin_cases j
    · change raw 1<_
      rw [source]
      exact shape _
    · change raw 2<_;rw [target];exact shape _
    · change raw 3<_;rw [amount];exact (private_count_room B p).trans_lt widthFit
  next=>exact Nat.two_pow_pos _

variable (unit : 0<B.reset.unit) (panels : Bool→B.reset.Fallback→DescentPackedFallbackTree.Panel (GroupStage.depthBound D n f g) count)
    (issued : PeerOrigins B pad prior unit panels) (oldBatch batch b : ℕ)
local notation "deck" => privateProjection (H:=H) (field:=field) B oldBatch batch b

/-- The literal lookup result on a reached raw host and its true original page. -/
def privateDigit (u : host₁) (side : Bool) (t : (Z).RootTicket T) (l : Fin capacity) (j : Fin 3) : Cell b :=
  (deck).scalar l j (prior.privatePages side t (DescentContactProbePitch.owner (named u.1.2))
    ((finProdFinEquiv (u.1.1,u.2)).cast (private_lane_size B)))

include issued in
theorem private_digits (u : host₁) (side : Bool) (t : (Z).RootTicket T) (slot : Fin capacity) (j : Fin 3)
    (shapeFit : shelf≤2^b) (widthFit : B.next.placement.cap<2^b) :
    (privateDigit B pad prior oldBatch batch b u side t slot j).val=
      let raw:=priorPrivate B pad prior (orig u) (receiverRoot B u).2 side t slot
      if raw 0=1 then raw ⟨j.val+1,by omega⟩ else 0 :=
  (private_row_numbers B pad prior oldBatch batch b u side t slot j).trans
    (Nat.mod_eq_of_lt (private_fields_fit B pad prior unit panels issued u side t slot b shapeFit widthFit j))

include issued in
theorem private_shape_lt (u : host₁) (s : Bool) (t : (Z).RootTicket T)
    (slot : Fin capacity) (j : Fin 3) (first : j.val<2) :
    (privateDigit B pad prior oldBatch batch b u s t slot j).val<shelf:=by
  let v:=orig u
  let g:=(receiverRoot B u).2
  let row:=priorPrivate B pad prior v g s t slot
  have exactRow:=private_row_numbers B pad prior oldBatch batch b u s t slot j
  rw [show (privateDigit B pad prior oldBatch batch b u s t slot j).val=_ from exactRow]
  refine (Nat.mod_le ..).trans_lt ?_
  change (if row 0=1 then row _ else 0)<shelf
  split
  next yes=>
    have shape:=private_raw_presence B unit s t v g slot (panels s) row
      (issued.numbers v g s t slot) (issued.installed v g s t slot)
    obtain ⟨p,hit⟩:=shape.1.mp yes
    obtain ⟨left,right⟩:=shape.2.2 p hit
    fin_cases j
    · change row 1<_
      rw [left]
      exact (coords ((blocks B).src (privateWire B p)).1.2).2.isLt
    · change row 2<_
      rw [right]
      exact (coords ((blocks B).dst (privateWire B p)).1.2).2.isLt
    · exact (Nat.lt_irrefl 2 first).elim
  next empty=>exact (by have:=two_le_roster_card (Z).graph r height;omega)

local notation "key₀" => localPrivateId r (2^(Z).n) capacity

/-- The finite hole test is applied at the same root ticket and wire ordinal as the private RAM deck. -/
def privateCandidate (u : host₁) (q : Fin (privateCount B)) (f₀ : Fin 3) : Cell b :=
  if hit : ∃p,key₀ p=q then
    let p:=hit.choose
    privateDigit B pad prior oldBatch batch b u p.1 p.2.1 p.2.2 f₀
  else 0

include issued in
theorem private_candidate_room (u : host₁) (q : Fin (privateCount B)) (j : Fin 3) (two : j.val<2) :
    (privateCandidate B pad prior oldBatch batch b u q j).val<shelf:=by
  unfold privateCandidate
  split
  · exact private_shape_lt B pad prior unit panels issued oldBatch batch b u _ _ _ j two
  · exact (by have:=two_le_roster_card (Z).graph r height;change 0<shelf;omega)

/-- Readback of the private projection on every installed actor and every finite job.
The original root data are independent of the new actor's sparse shape. -/
theorem private_candidate_read (pitch₁ : DescentContactPreROM.Layout)
    (hs : H=pitch₁.hosts) (gs : J=pitch₁.groups) (pal : shelf=pitch₁.shapes)
    (raw : Bool→(Z).RootTicket T→Fin pitch₁.hosts→Fin pitch₁.groups→Cell (deck).panels)
    (stored : ∀s t w₀ g₀,raw s t w₀ g₀=prior.privatePages s t (w₀.cast hs.symm) (g₀.cast gs.symm))
    (u : host₁) (q : Fin (privateCount B)) (j : Fin 3) :
    (deck).measured pitch₁ raw q j ((named u.1.2).cast (congrArg₂ Nat.mul hs pal))
        ((finProdFinEquiv (u.1.1,u.2)).cast ((private_lane_size B).trans gs)) =
      privateCandidate B pad prior oldBatch batch b u q j :=by
  have same (v : Fin pitch) :
      (DescentContactProbePitch.owner (v.cast (congrArg₂ Nat.mul hs pal))).cast hs.symm =
        DescentContactProbePitch.owner v:=by
    apply Fin.ext
    change v.val/pitch₁.shapes=v.val/shelf
    exact congrArg (fun width : ℕ => v.val / width) pal.symm
  by_cases found : ∃p,key₀ p=q
  · obtain ⟨⟨side,t,slot⟩,rfl⟩ := found
    apply Eq.trans ((deck).measured_true pitch₁ raw side t slot j
      ((named u.1.2).cast (congrArg₂ Nat.mul hs pal))
      ((finProdFinEquiv (u.1.1,u.2)).cast ((private_lane_size B).trans gs)))
    rw [stored, same]
    unfold privateCandidate
    split
    · rename_i hit
      rw [(key₀).injective hit.choose_spec]
      rfl
    · rename_i absent
      exact (absent ⟨_,rfl⟩).elim
  · have noDeck : ¬ ∃p,localPrivateId (deck).residual (deck).ports (deck).cap p=q := found
    unfold privateCandidate DescentPrivateMaskDeck.Shape.measured
    rw [dite_eq_right noDeck, dite_eq_right found]
    rfl

include issued in
theorem private_compact_shape (group : Fin groups₁) (x : Fin (2^k))
    (h₀ : Fin (Fintype.card B.next.V)) (q : Fin (privateCount B)) (j : Fin 3) (two:j.val<2) :
    let v:=(compactActorOrder B pad).symm h₀
    (privateCandidate B pad prior oldBatch batch b ((group,v),x) q j).val<shelf :=
  private_candidate_room B pad prior unit panels issued oldBatch batch b _ q j two

include issued in
/-- Every occupied root, padded wire slot, and absent physical root in the private
sector is decided by the three genuine native header digits. -/
theorem private_digits_meta (u : host₁) (s : Bool) (t : (Z).RootTicket T) (l : Fin capacity) (x : Fin 9→Cell b)
    (shapeFit : shelf≤2^b) (widthFit : B.next.placement.cap<2^b)
    (rad halo : ℕ) (rpos : 0<rad)
    (width : (x 0).val=(privateDigit B pad prior oldBatch batch b u s t l 2).val)
    (units : (x 8).val=(x 0).val)
    (src : (x 1).val=rad*(privateDigit B pad prior oldBatch batch b u s t l 0).val+halo)
    (dst : (x 2).val=rad*(privateDigit B pad prior oldBatch batch b u s t l 1).val+halo)
    (here : (x 3).val=rad*relativeShape B u+halo)
    (ranks : ∀p,localOrigin B u (privateShelfIndex B (localPrivateId _ _ capacity (s,t,l)))=some p →
      (x 4).val=localClass B u ((blocks B).src p.val) ∧ (x 5).val=localClass B u ((blocks B).dst p.val) ∧
        (x 6).val=localClass B u u)
    (self : (x 7).val≠0 ↔ u∉Stage.near B.next.placement u) :
    DescentCandidateMaskRAM.render x=DescentResetFieldAssembler.raw b
      («meta» B u (localOrigin B u (privateShelfIndex B (localPrivateId _ _ capacity (s,t,l))))) :=by
  let v:=orig u
  let g:=(receiverRoot B u).2
  let raw:=priorPrivate B pad prior v g s t l
  have read j:=private_digits B pad prior unit panels issued oldBatch batch b u s t l j shapeFit widthFit
  apply private_reached_meta B u s t l (panels s) raw x unit (issued.numbers v g s t l)
    (issued.installed v g s t l) rad halo rpos (width.trans (read 2)) units _ _ here ranks self
  · exact src.trans (congrArg (fun v=>rad*v+halo) (read 0))
  · exact dst.trans (congrArg (fun v=>rad*v+halo) (read 1))

theorem private_gap {b : ℕ} (u : host₁) (q : Fin (privateCount B)) (x : Fin 9→Cell b)
    (absent : ∀p,localPrivateId r (2^(Z).n) capacity p≠q) (width : (x 0).val=0) :
    DescentCandidateMaskRAM.render x=DescentResetFieldAssembler.raw b («meta» B u (localOrigin B u (privateShelfIndex B q))) :=by
  have gone : localOrigin B u (privateShelfIndex B q)=none:=by
    cases result:localOrigin B u (privateShelfIndex B q) with
    | none=>rfl
    | some e=>
      obtain ⟨y,_,key⟩:=(private_shelf_iff B u q e).1 result
      exact (absent _ key).elim
  rw [DescentCandidateMaskRAM.vacant_or_empty x (Or.inl width),gone]
  rfl


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

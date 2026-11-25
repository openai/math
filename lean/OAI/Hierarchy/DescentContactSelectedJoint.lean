import OAI.Hierarchy.DescentContactReachedJoints
import OAI.Hierarchy.DescentContactCastInputs
import OAI.Hierarchy.DescentContactDonorReached

namespace OAI
/-! # The three numerical contact coordinates on the true original socket -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup DescentResetLocalRoster
open DescentContactDonorSelection DescentContactCoordinateJoint DescentContactOutputShape
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
local notation "width" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "rad" => 2^(Nat.clog 2 ((A).degree+2))
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "N" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(A).cap)
local notation:max "site" s:arg c:arg => (if s then (blocks B).dst (contactParent B c) else (blocks B).src (contactParent B c))
local notation:max "center" s:arg c:arg => ((Z).rootVertex T ((R).owner s c),(Z).rootBlock T ((R).owner s c))
variable (H M field query cargo groups newBlocks batch marker «meta» : ℕ)

def contactOutputs : Shape:=
  ⟨donorFront B H M field query cargo,width,groups,newBlocks,batch,marker,«meta»⟩

local notation "X" => contactOutputs B H M field query cargo groups newBlocks batch marker «meta»


theorem selected_contact_joint (u : Host) (v : Fin (X).sparseHosts) (l : Block (T).commonDepth) (t : Fin (contactCount B))
    (data_ : (X).RawIndicators t) (s : Bool) (c : (R).Contact)
    (root : receiverRoot B u=center s c) (named : donor_query B t=(s,(Z).senderJoint T s c))
    (positive : 0<(blocks B).count (contactParent B c))
    (own : ∀j,(data_.own j v l).val=(originalDonor B u s j).elim 0 (fun e=>(Z).senderJoint T s ((R).contact e)))
    (mark : ∀j,(data_.marker j v l).val=contactSheet B u t (finProdFinEquiv (finTwoEquiv.symm s,j)))
    (shape : (data_.shape v l).val=relativeShape B u)
    (halos : ∀j e,originalDonor B u s j=some e→∀end_,(data_.halo end_ j v l).val=haloNumber B u (center end_ ((R).contact e)).1+1)
    (keyFits : (Z).senderJoint T s c<2^field) (packed : width*rad≤2^«meta») (which : Option Bool) :
    ((data_.indicators.selected which v l).val)=
      (match which with
      | none=>jointNumber B u (receiverRoot B u).1 (relativeShape B u)
      | some e=>if relativeShape B (site s c)=relativeShape B u then
          jointNumber B u (center e c).1 (relativeShape B (site e c)) else 0):=by
  let x:=data_.indicators
  let hereShape:=relativeShape B u
  have ranked : (X).request t=(Z).senderJoint T s c:=congrArg Prod.snd named
  have side : ((X).socketWing t).1=s:=congrArg Prod.fst named
  have keyPos : 0<(Z).senderJoint T s c:=Nat.pos_of_ne_zero (sender_not_zero B s c)
  have one : 1<2^field:=Nat.lt_of_le_of_lt keyPos keyFits
  have room (u' : Host) : relativeShape B u'<width:=((Z).hostFields T (B.frame.host.symm.toEmbedding.trans input.vertex) u'.1.2).2.isLt
  have covers (y a : ℕ) (hy : y<width) (ha : a<rad) : number rad y a<2^«meta»:=by
    calc number rad y a < y*rad+rad:=by unfold number;rw [Nat.mul_comm rad y];omega
         _=(y+1)*rad:=(Nat.succ_mul ..).symm
         _≤width*rad:=Nat.mul_le_mul_right _ hy
         _≤2^«meta»:=packed
  have found:=contact_witness B c positive
  obtain ⟨o,oc⟩:=found
  obtain ⟨ix,stored⟩:=originalDonor_exists B u s c root o (congrArg ((R).owner s) oc)
  have narrow (end_ : Bool) : haloNumber B u (center end_ c).1+1<rad:=by
    have belongs:=endpoint_mem B u s o ix stored end_
    rw [oc] at belongs
    exact halo_radix B u _ belongs
  have wide : width≤2^«meta»:=by
    exact (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans packed
  have zeroShape : (x.here v l).val=hereShape:=by
    change (((data_.shape v l).val:Cell «meta»)).val=_
    rw [shape,Fin.val_cast_of_lt ((room u).trans_le wide)]
  have probe : probeId B (endpointProbe B s c)=t:=
    donor_query_injective B ((query_probe B s c).trans named.symm)
  let expected : ℕ:=match which with
    | none=>jointNumber B u (receiverRoot B u).1 hereShape
    | some e=>if relativeShape B (site s c)=hereShape then jointNumber B u (center e c).1 (relativeShape B (site e c)) else 0
  have center_ : (receiverRoot B u).1=(center s c).1:=congrArg Prod.fst root
  have lim : expected<2^«meta»:=by
    cases which with
    | none=>simpa only [expected,jointNumber,center_] using covers _ _ (room u) (narrow s)
    | some e =>
      by_cases fits : relativeShape B (site s c) = hereShape
      · simpa only [expected,ite_eq_left fits,jointNumber] using covers _ _ (room (site e c)) (narrow e)
      · simpa only [expected,ite_eq_right fits] using Nat.two_pow_pos «meta»
  let target : Cell «meta»:=⟨expected,lim⟩
  change (visits ((X).request t) (fun j=>x.own j v l) (fun j=>x.item which j v l)).val=expected
  rw [ranked]
  change (visits _ _ _).val=target.val
  apply congrArg Fin.val
  apply pick_socket B u s c root ⟨o,oc⟩ _ _ target own
  intro j e row whose
  have marker_:=own_socket_marker B u s j e row
  simp only [whose,probe] at marker_
  have actual:= (mark j).trans marker_
  have halo (side_ : Bool) : (x.halo side_ j v l).val=haloNumber B u (center side_ c).1+1:=by
    have seen:=halos j e row side_
    simp only [whose] at seen
    change (((data_.halo side_ j v l).val:Cell «meta»)).val=_
    rw [seen,Fin.val_cast_of_lt]
    exact (narrow side_).trans_le (by
      have widthPos:=room u
      exact (Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt widthPos)).trans packed)
  have localJoint : (x.atEnd s j v l).val=jointNumber B u (center s c).1 hereShape:=by
    change (join rad (x.shape s j v l) (x.halo s j v l)).val=_
    have loc : x.shape s j v l=x.here v l:=by simp [Shape.Indicators.shape,side]
    rw [loc]
    change ((number rad (x.here v l).val (x.halo s j v l).val : Cell «meta»)).val = _
    rw [zeroShape,halo]
    exact Fin.val_cast_of_lt (covers _ _ (room u) (narrow s))
  cases which with
  | none =>
    apply Fin.ext
    simpa only [Shape.Indicators.item,side,expected,target,center_] using localJoint
  | some end_=>
    have nonzero : (Z).senderJoint T s c≠0:=Nat.ne_of_gt keyPos
    by_cases live : relativeShape B (site s c)=hereShape
    · have markRead:(data_.marker j v l).val=1+(contactOldPort B s e).val*width+relativeShape B (site (!s) c):=by simpa [hereShape,live] using actual
      have nz : data_.marker j v l≠0:=by intro eqn;rw [eqn,Fin.val_zero] at markRead;omega
      have yes : (x.used j v l).val=1 := by
        change (if data_.marker j v l = 0 then (0 : Cell field) else 1).val = 1
        rw [ite_eq_right nz]
        exact Fin.val_cast_of_lt one
      have gate:(x.ticket j v l).val=(Z).senderJoint T s c:=by
        change (((((X).request t : ℕ) : Cell field) * (((x.used j v l).val : ℕ) : Cell field))).val = _
        rw [yes,ranked]
        change ((((Z).senderJoint T s c : Cell field) * 1)).val = _
        rw [mul_one]
        exact Fin.val_cast_of_lt keyFits
      have remoteRead:(x.remote j v l).val=relativeShape B (site (!s) c):=
        DescentContactMarkerShape.exact_shape markRead (room _) ((room _).trans_le wide)
      have extracted : (x.shape end_ j v l).val=relativeShape B (site end_ c):=by
        by_cases here_ : end_=s
        · subst end_
          unfold Shape.Indicators.shape
          rw [side,ite_eq_left rfl]
          exact zeroShape.trans live.symm
        · have opposite : ∀ a b : Bool, a ≠ b → a = !b := by decide
          have rev := opposite end_ s here_
          unfold Shape.Indicators.shape
          rw [side,ite_eq_right here_,rev]
          exact remoteRead
      apply Fin.ext
      change (keep _ (x.ticket j v l) (x.atEnd end_ j v l)).val=expected
      rw [keep,ite_eq_left ⟨gate.trans ranked.symm,fun ez => nonzero (gate.symm.trans ez)⟩]
      change ((number rad (x.shape end_ j v l).val (x.halo end_ j v l).val : Cell «meta»)).val = expected
      rw [extracted,halo]
      simpa only [expected,ite_eq_left live,jointNumber] using
        Fin.val_cast_of_lt (covers _ _ (room (site end_ c)) (narrow end_))
    · have no:(data_.marker j v l).val=0:=by simpa [hereShape,live] using actual
      have none_ : data_.marker j v l=0:=Fin.ext no
      have absent : x.used j v l=0:=by simp [x,Shape.RawIndicators.indicators,DescentContactMarkerShape.flag,none_]
      apply Fin.ext
      simp [Shape.Indicators.item,keep,Shape.Indicators.ticket,absent,expected,live,target]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

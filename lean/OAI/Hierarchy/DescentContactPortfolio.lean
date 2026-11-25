import OAI.Hierarchy.DescentReachedContactDonor
import OAI.Hierarchy.DescentResetPeerCodes
import OAI.Hierarchy.DescentResetStemHostRank

namespace OAI
/-! # Raw contact peer incidence from old signed tickets on the bounded receiver grid -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt
open DescentCompiler DescentColonies DescentGL DescentChosenRouter DescentSharedCableNames
open DescentGroupPeerOrder DescentIssuedFallbackPanel DescentReservedPeerMarker DescentResetLocalRoster
open DescentDenseHostOrder DescentResetAttachments DescentResetPeerUnionRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "E" => (old).graph.Edge
local notation "Y" => 2^(Z).n
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(A).cap)
local notation "own" s:arg t:arg => (R).owner s t
local notation "root" s:arg t:arg => ((Z).rootVertex T (own s t),(Z).rootBlock T (own s t))
local notation "joint" => (Z).senderJoint T
local notation "site" s:arg c:arg => (if s then (blocks B).dst (contactParent B c) else (blocks B).src (contactParent B c))
local notation "before" => input.order.trans Fin.valEmbedding
local notation "ids" => input.vertex.trans Fin.valEmbedding
local notation "gkey" => Fin.valEmbedding (n:=S.groupCount i)
local notation "names" => cableNames k (groupRank gkey ids)
local notation "bank" => (R).Contact

/-- This is the neighbor field of the actual signed grain. Both polarities use the old port list,
also when an old wire has coincident end hosts. -/
def contactOldPort (s : Bool) (e : E) : Fin (A).degree :=
  let p:=port A s (beforeStem B e)
  (Stage.live A before S input.valid names p.1 p.2).neighbor

theorem contact_port_read (s : Bool) (e : E) :
    hostRoster A ids (B.frame.host.symm (root s ((R).contact e)).1) (contactOldPort B s e)=
      some (B.frame.host.symm (root (!s) ((R).contact e)).1) := by
  have position (t : Bool) :
      B.frame.host.symm (root t ((R).contact e)).1=((A).pos (endSite A t (beforeStem B e))).2 := by
    rw [congrArg Prod.fst (contact_stem_root B t e),B.frame.homeHost,beforeStem_end B,
      Equiv.symm_apply_apply]
  rw [position,position]
  let p:=port A s (beforeStem B e)
  let chip:=Stage.live A before S input.valid names p.1 p.2
  have face : chip.target=s:=by cases s <;> rfl
  have actual:=signedPeer_actual A before S input.valid names s (beforeStem B e)
  change signedPeer A before S input.valid names s p.1
    (Stage.signed A before S input.valid p.1.1 p.1.2 p.2)=_ at actual
  simp only [signedPeer,Stage.signed_read] at actual
  change (if chip.target=s then physicalPeer A names p.1 chip.neighbor else none)=_ at actual
  rw [ite_eq_left face,physicalPeer_group A gkey ids] at actual
  apply_fun Option.map (fun a : Stage.Host _ _ k=>a.1.2) at actual
  simpa [chip,p,port_fst,Function.comp_def,contactOldPort,Stage.home] using actual

def contactTicketDigit : bank→ℕ
  | .inl t=>t.2.val
  | .inr _=>0

def contactPairSpan : bank→ℕ
  | .inl t=>(R).span t.1
  | .inr _=>0

abbrev ContactProbe := Bool×Root r Y×Fin (Y+2^height)

def probeId : ContactProbe B↪Fin (contactCount B) := localPrivateId r Y (Y+2^height)

def contactRowMark (u : Host) (probe : ContactProbe B) (e : E) : ℕ :=
  let t:=(R).contact e
  let side:=probe.1
  mark (Z).graph r height side probe.2.1 probe.2.2 (relativeShape B u)
    (joint side t) (joint (!side) t) (contactTicketDigit B t) (contactPairSpan B t)
    ((Z).contactDepth side t) ((Z).contactDepth (!side) t) (contactOldPort B side e).val

def contactSheet (u : Host) (key : Fin (contactCount B)) (donor : Fin (stemsCount B)) : ℕ :=
  if live : ∃p,probeId B p=key then
    let p:=live.choose
    let j : Fin 2×Fin half:=finProdFinEquiv.symm donor
    if finTwoEquiv j.1=p.1 then (originalDonor B u p.1 j.2).elim 0 (contactRowMark B u p) else 0
  else 0

theorem contactSheet_read (u : Host) (p : ContactProbe B) (j : Fin half) :
    contactSheet B u (probeId B p) (finProdFinEquiv (finTwoEquiv.symm p.1,j))=
      (originalDonor B u p.1 j).elim 0 (contactRowMark B u p) := by
  have yes : ∃a,probeId B a=probeId B p:=⟨p,rfl⟩
  simp [contactSheet]

theorem contactSheet_donor (u : Host) (key : Fin (contactCount B)) (donor : Fin (stemsCount B))
    (hit : contactSheet B u key donor≠0) :
    ∃(p : ContactProbe B) (j : Fin half) (e : E),originalDonor B u p.1 j=some e ∧
      contactSheet B u key donor=contactRowMark B u p e := by
  by_cases existsQ : ∃p,probeId B p=key
  · let p:=existsQ.choose
    let j : Fin 2×Fin half:=finProdFinEquiv.symm donor
    by_cases same : finTwoEquiv j.1=p.1
    · have read : contactSheet B u key donor=(originalDonor B u p.1 j.2).elim 0 (contactRowMark B u p) := by
        unfold contactSheet
        rw [dite_eq_left existsQ]
        exact ite_eq_left same
      cases orig : originalDonor B u p.1 j.2 with
      | none=>simp [read,orig] at hit
      | some e=>exact ⟨p,j.2,e,orig,by simp [read,orig]⟩
    · have miss : contactSheet B u key donor=0 := by
        unfold contactSheet
        rw [dite_eq_left existsQ]
        exact ite_eq_right same
      exact (hit miss).elim
  · exact (hit (by simp [contactSheet,existsQ])).elim

private theorem mark_sound (u : Host) (p : ContactProbe B) (j : Fin half) (e : E)
    (hit : originalDonor B u p.1 j=some e) (nonzero : contactRowMark B u p e≠0) :
    ∃c : bank,(∀s,own s c=own s ((R).contact e)) ∧ site p.1 c=u ∧
      contactRowMark B u p e=1+(contactOldPort B p.1 e).val*shelf+relativeShape B (site (!p.1) c) := by
  let t:=(R).contact e
  have valid (a) (same : t=.inl a) : contactTicketDigit B t=a.2.val ∧ contactPairSpan B t=(R).span a.1:=by rw [same];exact ⟨rfl,rfl⟩
  obtain ⟨c,owners,_,_,shape,price⟩:=raw_contact_sound B p.1 t p.2.1 p.2.2 (relativeShape B u)
    (contactTicketDigit B t) (contactPairSpan B t) (contactOldPort B p.1 e).val valid nonzero
  have oldLoc:=contact_old_slot_location B u p.1 (finProdFinEquiv.symm j) e hit
  have contactLoc:=contact_endpoint_root B c p.1
  have geo : root p.1 c=root p.1 t:=congrArg (fun a=>((Z).rootVertex T a,(Z).rootBlock T a)) (owners p.1)
  exact ⟨c,owners,root_shape_injective B (contactLoc.trans (geo.trans oldLoc.symm)) shape.symm,price⟩

private theorem mark_complete (s : Bool) (c : bank) :
    let u:=site s c
    ∃(key : Fin (contactCount B)) (l : Fin (stemsCount B)) (e : E),
      (∀a,own a c=own a ((R).contact e)) ∧
      contactSheet B u key l=1+(contactOldPort B s e).val*shelf+relativeShape B (site (!s) c) := by
  intro u
  obtain ⟨j,e,hit,owns,receipt⟩:=marker_donor_exists B u s c (contact_endpoint_root B c s)
  let t:=(R).contact e
  let p : ContactProbe B:=⟨s,(Z).rootTicket T (own s c),⟨_,(Z).contactSlotWord_lt T s c⟩⟩
  refine ⟨probeId B p,finProdFinEquiv (finTwoEquiv.symm s,j),e,fun a=>(owns a).symm,?_⟩
  have real:=receipt (contactTicketDigit B t) (contactPairSpan B t) (contactOldPort B s e).val (by
    rintro a eqn
    change t=.inl a at eqn
    rw [eqn]
    exact ⟨rfl,rfl⟩)
  rw [contactSheet_read]
  change (originalDonor B u s j).elim 0 (contactRowMark B u p)=_
  rw [hit]
  exact real

variable {H : ℕ} (pad : Fintype.card input.V≤H)
local notation "origin" => input.vertex.trans (Fin.castLEEmb pad)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans origin
local notation "rank" => (Z).rawHostRank T vertex
local notation "fields" => (Z).hostFields T vertex
variable (peers : Fin H→Fin input.placement.degree→Option (Fin H))
variable (rosterRead : ∀(v : input.V) j,peers ((input.vertex v).castLE pad) j=(hostRoster input.placement (input.vertex.trans Fin.valEmbedding) v j).map (input.vertex.trans (Fin.castLEEmb pad)))
include rosterRead

private theorem candidate_at (s : Bool) (c : bank) (e : E) (same : ∀a,own a c=own a ((R).contact e))
    (x : Fin (H*shelf)) :
    (∃j,Candidates.candidate peers (rank (site s c).1.2) j=some x ∧
      1+(contactOldPort B s e).val*shelf+relativeShape B (site (!s) c)=j.val+1) ↔ rank (site (!s) c).1.2=x := by
  let u:=site s c
  let v:=site (!s) c
  let off:=contactOldPort B s e
  have occupied (a : Bool) :
      (receiverRoot B (site a c)).1=(root a ((R).contact e)).1:=
    (congrArg Prod.fst (contact_endpoint_root B c a)).trans (congrArg ((Z).rootVertex T) (same a))
  have oldPort : peers (fields u.1.2).1 off=some (fields v.1.2).1 := by
    change peers (origin (B.frame.host.symm (receiverRoot B u).1)) off=some (origin (B.frame.host.symm (receiverRoot B v).1))
    refine (rosterRead (B.frame.host.symm (receiverRoot B u).1) off).trans ?_
    have src := congrArg B.frame.host.symm (occupied s)
    have dst := congrArg B.frame.host.symm (occupied (!s))
    have got := contact_port_read B s e
    have oldPortAt : hostRoster A ids (B.frame.host.symm (receiverRoot B u).1) off =
        some (B.frame.host.symm (receiverRoot B v).1) :=
      (congrArg (fun q => hostRoster A ids q off) src).trans (got.trans (congrArg some dst.symm))
    exact congrArg (Option.map (origin)) oldPortAt
  change (∃j,Candidates.candidate peers (rank u.1.2) j=some x ∧
    1+off.val*shelf+(fields v.1.2).2.val=j.val+1) ↔ rank v.1.2=x
  rw [show 1+off.val*shelf+(fields v.1.2).2.val=off.val*shelf+(fields v.1.2).2.val+1 by omega,
    Candidates.socket_value]
  change (peers (finProdFinEquiv.symm (finProdFinEquiv (fields u.1.2))).1 off).map _=_
    ↔ finProdFinEquiv (fields v.1.2)=x
  rw [Equiv.symm_apply_apply,oldPort]
  simp

/-- Positive marker values are precisely one plus the bounded candidate ordinal. The equivalence
ranges over every structural installed contact, including reserved cables of width zero. -/
theorem contact_tickets (v : B.next.V) (x : Fin (H*shelf)) :
    (∃(key : Fin (contactCount B)) (don : Fin (stemsCount B)) (gp : Fin groups) (lo : Block k) (j : Fin (Candidates.count shelf input.placement.degree)),
      Candidates.candidate peers (rank v) j=some x ∧ contactSheet B ((gp,v),lo) key don=j.val+1) ↔
      ∃c : bank,rawPeer B (contactParent B c) (rank v).val x.val := by
  constructor
  · rintro ⟨key,don,gp,lo,j,chosen,numeric⟩
    let u : Host:=((gp,v),lo)
    obtain ⟨p,l,e,hit,price⟩:=contactSheet_donor B u key don (by rw [numeric];omega)
    obtain ⟨c,same,start,amount⟩:=mark_sound B u p l e hit (by rw [←price,numeric];omega)
    have slotEq : 1+(contactOldPort B p.1 e).val*shelf+relativeShape B (site (!p.1) c)=j.val+1:=
      amount.symm.trans (price.symm.trans numeric)
    have endpoint : (rank (site (!p.1) c).1.2)=x:=
      (candidate_at B pad peers rosterRead p.1 c e same x).mp
        ⟨j,by rw [start];exact chosen,slotEq⟩
    refine ⟨c,(padded_peer_words B (contactParent B c) pad _ _).mpr ?_⟩
    have left : (rank (site p.1 c).1.2).val=(rank v).val:=by rw [start]
    cases face : p.1 <;> simp only [face,Bool.not_false,Bool.not_true,ite_true] at left endpoint
    · exact Or.inl ⟨left,congrArg Fin.val endpoint⟩
    · exact Or.inr ⟨left,congrArg Fin.val endpoint⟩
  · rintro ⟨c,raw⟩
    have emit (s : Bool) (left : (rank (site s c).1.2).val=(rank v).val)
        (right : (rank (site (!s) c).1.2).val=x.val) :
        ∃(key : Fin (contactCount B)) (don : Fin (stemsCount B)) (gp : Fin groups) (lo : Block k) (j : Fin (Candidates.count shelf input.placement.degree)),
          Candidates.candidate peers (rank v) j=some x ∧ contactSheet B ((gp,v),lo) key don=j.val+1 := by
      let u:=site s c
      have vertexEq : u.1.2=v:=(rank).injective (Fin.ext left)
      obtain ⟨key,don,e,same,numeric⟩:=mark_complete B s c
      obtain ⟨j,ok,num⟩:=(candidate_at B pad peers rosterRead s c e same x).mpr (Fin.ext right)
      refine ⟨key,don,u.1.1,u.2,j,?_,?_⟩
      · change Candidates.candidate peers (rank u.1.2) j=some x at ok
        rwa [vertexEq] at ok
      · have point : ((u.1.1,v),u.2)=u:=by rw [←vertexEq]
        rw [point]
        exact numeric.trans num
    rcases (padded_peer_words B (contactParent B c) pad _ _).mp raw with a|a
    · exact emit false a.1 a.2
    · exact emit true a.1 a.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

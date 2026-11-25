import OAI.Hierarchy.DescentReservedSocketTranslation
import OAI.Hierarchy.DescentResetContactShapePayload

namespace OAI
/-! # Reading a structural contact from a prior signed donor, including empty reserved sockets -/
namespace Hierarchy.DescentReservedSocketPanel
open DescentResetLocalRoster DescentResetParentCodec DescentResetPublicParentWord DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

/-- The first two inputs are the genuinely issued one-based directed tickets at the two old ends.
The last two inputs are the paid donor's serial modulo the pair span, and that span. -/
def peer (r Y Ht : ℕ) (target : Root r Y) (socket own remote serial span : ℕ) : ℕ :=
  let shape : Shape:=⟨0,r,Y,0,0,0,0⟩
  match unpack shape Ht own,unpack shape Ht remote with
  | some (q,a),some (q',b)=>
    if q≠target then 0 else
    match q with
    | .inl _=>
      let start:=a-serial
      let j:=socket-start
      if start≤ socket ∧ j<span then (rootId r Y q').val*(Y+2^Ht)+(b-serial+j)+1 else 0
    | .inr _=>if socket=a then remote else 0
  | _,_=>0

theorem empty (r Y Ht : ℕ) (q : Root r Y) (socket remote serial span : ℕ) :
    peer r Y Ht q socket 0 remote serial span=0 := by
  have absent : unpack ⟨0,r,Y,0,0,0,0⟩ Ht 0=none:=by unfold unpack;split <;> simp
  simp [peer,absent]

open DescentChosenRouter DescentColonies DescentSixParty
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Z.Terminals)
local notation "R" => Z.placement
local notation "Y" => 2^Z.n
local notation "r" => Z.k-T.commonDepth
local notation "book" => T.columns
local notation "slot" => Z.contactSlotWord T
local notation "root" => fun s c=>Z.rootTicket T ((R).owner s c)
local notation "joint" => Z.senderJoint T

theorem donor_decode (s : Bool) (c : (R).Contact) :
    unpack ⟨0,r,Y,0,0,0,0⟩ Ht (joint s c)=some (root s c,slot s c) :=
  unpacked _ _ _ _

theorem good_sibling (s : Bool) (t : Reserve (R).span) (j : Fin ((R).span t.1)) :
    let c : (R).Contact:=.inl t
    let other : (R).Contact:=.inl ⟨t.1,j⟩
    peer r Y Ht (root s other) (slot s other) (joint s c) (joint (!s) c) t.2.val ((R).span t.1)=joint (!s) other := by
  intro c other
  have atOwn:=Placement.ColumnRoster.translate (R) book s t j
  have atPeer:=Placement.ColumnRoster.translate (R) book (!s) t j
  change slot s c-t.2.val+j.val=slot s other at atOwn
  change slot (!s) c-t.2.val+j.val=slot (!s) other at atPeer
  have rootOwn : root s c=root s other:=rfl
  have lo : slot s c-t.2.val≤ slot s other:=by omega
  have exactJ : slot s other-(slot s c-t.2.val)=j.val:=by omega
  simp only [peer,donor_decode,rootOwn,ne_eq,not_true_eq_false,ite_false]
  change (if slot s c-t.2.val≤ slot s other ∧ slot s other-(slot s c-t.2.val)<(R).span t.1 then _ else 0)=_
  rw [exactJ,ite_eq_left ⟨lo,j.isLt⟩,atPeer]
  rfl

theorem fallback (s : Bool) (t) (serial span : ℕ) :
    let c : (R).Contact:=.inr t
    peer r Y Ht (root s c) (slot s c) (joint s c) (joint (!s) c) serial span=joint (!s) c := by
  intro c
  simp only [peer,donor_decode,ne_eq,not_true_eq_false,ite_false]
  cases s <;> exact ite_eq_left trivial

/-- On any nonzero marker the donor's own reservation contains an actual structural edge at the
requested socket. The peer word it returns is attached to that very edge. -/
theorem good_sound (s : Bool) (t : Reserve (R).span) (q : Root r Y) (col : ℕ)
    (hit : peer r Y Ht q col (joint s (.inl t)) (joint (!s) (.inl t)) t.2.val ((R).span t.1)≠0) :
    ∃j : Fin ((R).span t.1),q=root s (.inl ⟨t.1,j⟩) ∧ col=slot s (.inl ⟨t.1,j⟩) ∧
      peer r Y Ht q col (joint s (.inl t)) (joint (!s) (.inl t)) t.2.val ((R).span t.1)=joint (!s) (.inl ⟨t.1,j⟩) := by
  have equal : root s (.inl t)=q:=by
    by_contra neq
    simp [peer,donor_decode,neq] at hit
  subst q
  have bounds : slot s (.inl t)-t.2.val≤col ∧ col-(slot s (.inl t)-t.2.val)<(R).span t.1:=by
    by_contra absent
    apply hit
    simp only [peer,donor_decode,ne_eq,not_true_eq_false,ite_false]
    change (if slot s (.inl t)-t.2.val≤col ∧ col-(slot s (.inl t)-t.2.val)<(R).span t.1 then _ else 0)=_
    exact ite_eq_right absent
  let j : Fin ((R).span t.1):=⟨_,bounds.2⟩
  have atSocket:=Placement.ColumnRoster.translate (R) book s t j
  change slot s (.inl t)-t.2.val+(col-(slot s (.inl t)-t.2.val))=slot s (.inl ⟨t.1,j⟩) at atSocket
  have same : col=slot s (.inl ⟨t.1,j⟩):=by omega
  refine ⟨j,rfl,same,?_⟩
  rw [same]
  exact good_sibling Z T s t j

theorem fallback_sound (s : Bool) (t) (q : Root r Y) (col serial span : ℕ)
    (hit : peer r Y Ht q col (joint s (.inr t)) (joint (!s) (.inr t)) serial span≠0) :
    q=root s (.inr t) ∧ col=slot s (.inr t) ∧
      peer r Y Ht q col (joint s (.inr t)) (joint (!s) (.inr t)) serial span=joint (!s) (.inr t) := by
  have equal : root s (.inr t)=q:=by
    by_contra neq
    simp [peer,donor_decode,neq] at hit
  subst q
  have atSocket : col=slot s (.inr t):=by
    by_contra absent
    apply hit
    simp only [peer,donor_decode,ne_eq,not_true_eq_false,ite_false]
    change (if col=slot s (.inr t) then _ else 0)=_
    exact ite_eq_right absent
  subst col
  exact ⟨rfl,rfl,fallback Z T s t serial span⟩

/-- Every nonzero probe is backed by some installed contact at this same owner root and queried
socket. Its opposite owner is the *donor's* opposite owner even for an unoccupied sibling. -/
theorem sound (s : Bool) (t : (R).Contact) (q : Root r Y) (col serial span : ℕ)
    (paid : ∀v,t=.inl v→serial=v.2.val ∧ span=(R).span v.1)
    (hit : peer r Y Ht q col (joint s t) (joint (!s) t) serial span≠0) :
    ∃v : (R).Contact,(∀a,(R).owner a v=(R).owner a t) ∧ q=root s v ∧ col=slot s v ∧
      peer r Y Ht q col (joint s t) (joint (!s) t) serial span=joint (!s) v := by
  cases t with
  | inl t=>
    obtain ⟨rfl,rfl⟩:=paid t rfl
    obtain ⟨j,own,loc,result⟩:=good_sound Z T s t q col hit
    exact ⟨.inl ⟨t.1,j⟩,fun _=>rfl,own,loc,result⟩
  | inr t=>
    obtain ⟨own,loc,result⟩:=fallback_sound Z T s t q col serial span hit
    exact ⟨.inr t,fun _=>rfl,own,loc,result⟩

/-- One real old paid input witnesses each member of its entire installed interval. Every
exceptional contact is itself formed by a real old input. -/
theorem covers {N : ℕ} {key : A.graph.Edge↪Fin N} (seen : (R).OrderedTickets key)
    (s : Bool) (v : (R).Contact) :
    ∃e : A.graph.Edge,let t:=(R).contact e
      (∀a,(R).owner a t=(R).owner a v) ∧
      ∀serial span : ℕ,(∀c,t=.inl c→serial=c.2.val ∧ span=(R).span c.1)→
        peer r Y Ht (root s v) (slot s v) (joint s t) (joint (!s) t) serial span=joint (!s) v := by
  cases v with
  | inl v=>
    rcases v with ⟨a,j⟩
    obtain ⟨p,hp⟩:=seen.pair_observed a
    subst a
    have actual : (R).contact p.val=.inl ((R).ticket p):=by simp [Placement.contact,contact,p.property]
    refine ⟨p.val,?_⟩
    dsimp only;rw [actual]
    refine ⟨fun _=>rfl,?_⟩
    intro serial span paid
    obtain ⟨rfl,rfl⟩:=paid _ rfl
    exact good_sibling Z T s ((R).ticket p) j
  | inr v=>
    rcases v with ⟨a,ha⟩
    obtain ⟨p,_,hp⟩:=Finset.mem_image.mp ha
    subst a
    have actual : (R).contact p.val=.inr ⟨_,ha⟩:=by simp [Placement.contact,contact,p.property]
    refine ⟨p.val,?_⟩
    dsimp only;rw [actual]
    exact ⟨fun _=>rfl,fun serial span _=>fallback Z T s _ serial span⟩

end
end Hierarchy.DescentReservedSocketPanel

end OAI

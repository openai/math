import OAI.Hierarchy.DescentRotorInstalledMatrix
import OAI.Hierarchy.DescentResetContactShapePayload
import OAI.Hierarchy.DescentResetStemRead

namespace OAI
/-! # Previous signed donor slots for occupied contacts and empty structural reservations -/
namespace Hierarchy.DescentSixParty.GroupStage

open DescentGL DescentColonies DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentChosenRouter
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "R" => Z.placement
local notation "c" => T.commonDepth
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "atSite" => DescentIssuedFallbackPanel.endSite A
local notation "own" => (R).owner
local notation "rootV" => fun z : (R).Site=>frm.host.symm (Z.rootVertex T z)
local notation "rootH" => Z.rootBlock T
local notation "rowAt" => donor digits frm.basis fit
local notation "entry" => atSlot A native S ready
local notation "landing" => localAddress («c»:=c) A native S ready digits frm.basis

theorem contact_sender_parameters (s : Bool) (e : Grain A) :
    let z : (R).Site := own s ((R).contact e)
    (A.pos (atSite s e)).2=rootV z ∧
      group c (rearrange frm.basis (oldBlock digits (home A (atSite s e))))=(rootH z).val := by
  change _=rootV (own s ((R).contact e)) ∧ _=(rootH (own s ((R).contact e))).val
  cases found : own s ((R).contact e) with
  | inl a =>
    exact rotorCellsAt A S ready digits Z T frm s a e found
  | inr t =>
    exact falls_parameters A S ready digits Z T frm (show falls A S ready Z s t e from found)

/-- The donor is the real signed slot at the old endpoint, including when the queried contact is a
different reserved socket with the same owner. -/
theorem contact_sender_at (s : Bool) (target : (R).Contact) (e : Grain A)
    (here : own s ((R).contact e)=own s target) :
    let j : Fin (2^(m-c)) × Fin (2*A.cap) := landing s e
    entry s (rowAt (rootV (own s target)) (rootH (own s target)) j.1) j.2=some e := by
  intro j
  have hp:=contact_sender_parameters A S ready digits Z T frm s e
  dsimp only at hp
  rw [here] at hp
  let a:=port A s e
  have atV : a.1.1.2=rootV (own s target) := by
    change (port A s e).1.1.2=_
    rw [port_fst]
    exact hp.1
  have atH : group c (rearrange frm.basis (oldBlock digits a.1))=(rootH (own s target)).val := by
    change group c (rearrange frm.basis (oldBlock digits (port A s e).1))=_
    rw [port_fst]
    exact hp.2
  apply (atSlot_iff A native S ready ..).2
  exact Prod.ext (donor_locates digits frm.basis fit a.1 _ _ atV atH).symm rfl

theorem contact_sender_slot (s : Bool) (target : (R).Contact) (e : Grain A)
    (here : own s ((R).contact e)=own s target) :
    ∃(lo : Fin (2^(m-c))) (slot : Fin (2*A.cap)),
      entry s (rowAt (rootV (own s target)) (rootH (own s target)) lo) slot=some e :=
  ⟨(landing s e).1,(landing s e).2,
    contact_sender_at A S ready digits native Z T frm s target e here⟩

/-- At any hit the donor's owner lives at the vertex and common block of this very rectangle.
Its relative root ticket can consequently distinguish full physical roots. -/
theorem contact_sender_located (s : Bool) (v : V) (hi : Block c) (lo : Fin (2^(m-c)))
    (slot : Fin (2*A.cap)) (e : Grain A) (found : entry s (rowAt v hi lo) slot=some e) :
    let z : (R).Site := own s ((R).contact e)
    Z.rootVertex T z=frm.host v ∧ rootH z=hi := by
  intro z
  have addr:=(atSlot_iff A native S ready ..).1 found
  have point : home A (atSite s e)=rowAt v hi lo :=
    (port_fst A s e).symm.trans (congrArg Prod.fst addr)
  have part:=contact_sender_parameters A S ready digits Z T frm s e
  have lowV : (A.pos (atSite s e)).2=v:=congrArg (fun a : Host J V k=>a.1.2) point
  constructor
  · exact (frm.host.apply_symm_apply _).symm.trans (congrArg frm.host (part.1.symm.trans lowV))
  · apply Fin.ext
    rw [←part.2,point]
    change group c (rearrange frm.basis (digits.symm (digits ((rearrange frm.basis).symm (join fit hi lo)))))=hi.val
    rw [Equiv.symm_apply_apply,Equiv.apply_symm_apply]
    exact congrArg Fin.val (DescentPlainTerminal.high_join fit hi lo)

/-- For a reserved ticket it is enough that an old signed grain belongs to its ordered pair. A
fallback ticket itself is the image of an old grain. -/
def supportsContact (target : (R).Contact) (e : Grain A) : Prop :=
  match target with
  | .inl j=>∃p,((R).ticket p).1=j.1 ∧ p.val=e
  | .inr t=>(R).contact e=.inr t

theorem structural_sender (target : (R).Contact) {M : ℕ} {key : (Wold).graph.Edge↪Fin M}
    (tickets : (R).OrderedTickets key) :
    ∃e : Grain A,supportsContact A S ready Z target e ∧ ∀s,
      own s ((R).contact e)=own s target ∧
        entry s (rowAt (rootV (own s target)) (rootH (own s target)) (landing s e).1)
          (landing s e).2=some e := by
  rcases target with ⟨a,j⟩|⟨t,seen⟩
  · obtain ⟨p,observed⟩:=tickets.pair_observed a
    refine ⟨p.val,⟨p,observed,rfl⟩,fun s=>?_⟩
    have owner : own s ((R).contact p.val)=own s (.inl ⟨a,j⟩) := by
      simp only [Placement.contact,DescentChosenRouter.contact,dite_eq_left p.property,Placement.owner,
        DescentChosenRouter.owner,observed]
    exact ⟨owner,contact_sender_at A S ready digits native Z T frm s _ _ owner⟩
  · obtain ⟨p,_,observed⟩:=Finset.mem_image.mp seen
    have real : (R).contact p.val=.inr ⟨t,seen⟩ := by
      rw [Placement.contact,DescentChosenRouter.contact,dite_eq_right p.property]
      exact congrArg Sum.inr (Subtype.ext observed)
    refine ⟨p.val,real,fun s=>?_⟩
    have owner:=congrArg (own s) real
    exact ⟨owner,contact_sender_at A S ready digits native Z T frm s _ _ owner⟩

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentChosenRouter DescentDenseHostOrder DescentContacts DescentContactReceiver
open DescentSharedCableNames DescentResetPublicParentWord DescentResetParentCodec
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "Y" => 2^(Z).n
local notation "r" => (Z).k-(T).commonDepth
local notation "height" => GroupStage.depthBound D n f g
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex

theorem sender_socket_word (s : Bool) (a : (R).Contact) :
    (socketId Y height (contactSocket B s a)).val=(Z).contactSlotWord T s a := by
  cases a with
  | inl a=>exact rotor_socket _
  | inr a=>exact tree_socket _

theorem contact_sender_unique (s : Bool) {a b : (R).Contact}
    (vertex : (Z).rootVertex T ((R).owner s a)=(Z).rootVertex T ((R).owner s b))
    (block : (Z).rootBlock T ((R).owner s a)=(Z).rootBlock T ((R).owner s b))
    (root : (Z).rootTicket T ((R).owner s a)=(Z).rootTicket T ((R).owner s b))
    (socket : (Z).contactSlotWord T s a=(Z).contactSlotWord T s b) : a=b := by
  apply contact_unique B s
  · apply ((Z).rootLocation T vertexCode).injective
    exact Prod.ext (congrArg vertexCode vertex) (Prod.ext block root)
  · apply (socketId Y height).injective
    exact Fin.ext ((sender_socket_word B s a).trans (socket.trans (sender_socket_word B s b).symm))

theorem contact_sender_word_unique (s : Bool) {a b : (R).Contact}
    (vertex : (Z).rootVertex T ((R).owner s a)=(Z).rootVertex T ((R).owner s b))
    (block : (Z).rootBlock T ((R).owner s a)=(Z).rootBlock T ((R).owner s b))
    (word : (Z).senderJoint T s a=(Z).senderJoint T s b) : a=b := by
  have dataEq:=congrArg (unpack ⟨0,r,Y,0,0,0,0⟩ height) word
  simp only [ResetInput.senderJoint,unpacked,Option.some.injEq,Prod.mk.injEq] at dataEq
  exact contact_sender_unique B s vertex block dataEq.1 dataEq.2

open DescentIssuedFallbackPanel DescentColonies DescentGL DescentResetAttachments
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "basis" => B.frame.basis
local notation "fit" => B.frame.enough.trans (Nat.sub_le ..)
local notation "before" => input.order.trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "m" => S.groupWidth k tail i+k
local notation "depth" => (T).commonDepth
local notation "Slot" => Fin (2^(m-depth))×Fin (2*(A).cap)
local notation "physicalRoot" => fun (s : Bool) (t : (R).Contact) => ((Z).rootVertex T ((R).owner s t),(Z).rootBlock T ((R).owner s t))

/-- Both the public gate and the stem use the original attachment's host and coarse block. The two
relative tickets may differ between a good rotor and the old terminal. -/
theorem contact_stem_root (s : Bool) (e : (old).graph.Edge) :
    let t:=(T).home (ends (old).graph s e)
    physicalRoot s ((R).contact e)=(((T).code t).1,(Z).rootBlock T (.inr t)) := by
  intro t
  have actual:=DescentChosenRouter.public_read (R) (T).code (T).source s e
  rw [←(T).attach] at actual
  have atV (p : (R).Public) :
      (Z).rootVertex T ((R).site s p)=(publicAddress (R) (T).code p).1 := by
    cases p <;> rfl
  have atHigh (p : (R).Public) :
      ((Z).rootBlock T ((R).site s p)).val=coarseName depth (publicAddress (R) (T).code p) := by
    cases p <;> rfl
  dsimp only
  rw [←(R).align s e]
  exact Prod.ext ((atV _).trans (congrArg Prod.fst actual))
    (Fin.ext ((atHigh _).trans (congrArg (coarseName depth) actual)))

/-- A hit in the already issued closed reset's old stem rectangle fixes both coordinates of its
contact owner. -/
theorem contact_old_slot_location (u : Host) (s : Bool) (j : Slot) (e : (old).graph.Edge)
    (hit : oldStemAt B u s j=some e) : receiverRoot B u=physicalRoot s ((R).contact e) :=
  (donor_root B u s j e hit).symm.trans (((stem_receiver_root B s e).1).trans (contact_stem_root B s e).symm)

theorem contact_old_at (u : Host) (s : Bool) (target : (R).Contact) (e : (old).graph.Edge)
    (rootGeom : receiverRoot B u=physicalRoot s target) (here : (R).owner s ((R).contact e)=(R).owner s target) :
    let j:=localAddress (c:=depth) A before S input.valid digitsIn basis s (beforeStem B e)
    oldStemAt B u s j=some e := by
  intro j
  let t:=(T).home (ends (old).graph s e)
  have center : receiverRoot B u=(((T).code t).1,(Z).rootBlock T (.inr t)) := by
    exact rootGeom.trans ((congrArg (fun z => ((Z).rootVertex T z, (Z).rootBlock T z)) here.symm).trans (contact_stem_root B s e))
  let p:=port A s (beforeStem B e)
  have atV : p.1.1.2=B.frame.host.symm (receiverRoot B u).1 := by
    change (port A s (beforeStem B e)).1.1.2=_
    rw [port_fst,center]
    change ((A).pos (endSite A s (beforeStem B e))).2=B.frame.host.symm (((T).code t).1)
    rw [beforeStem_end B]
    apply B.frame.host.injective
    rw [Equiv.apply_symm_apply]
    exact (B.frame.homeHost _).symm
  have atH : group depth (rearrange basis (oldBlock digitsIn p.1))=(receiverRoot B u).2.val := by
    change group depth (rearrange basis (oldBlock digitsIn (port A s (beforeStem B e)).1))=_
    rw [port_fst,center]
    change group depth (rearrange basis (StarKeys.filled W.graph (A).pos (A).block digitsIn
      (endSite A s (beforeStem B e))))=coarseName depth ((T).code t)
    rw [beforeStem_end B]
    exact (B.frame.homeHigh _).symm
  have oldHit : stemDonor B u s j=some (beforeStem B e) := by
    apply (atSlot_iff A before S input.valid ..).2
    exact Prod.ext (donor_locates digitsIn basis fit p.1 _ _ atV atH).symm rfl
  unfold oldStemAt
  rw [oldHit]
  exact congrArg some ((priorGrain B).symm_apply_apply e)

theorem contact_old_slot (u : Host) (s : Bool) (target : (R).Contact) (e : (old).graph.Edge)
    (rootGeom : receiverRoot B u=physicalRoot s target) (here : (R).owner s ((R).contact e)=(R).owner s target) :
    ∃j : Slot,oldStemAt B u s j=some e :=
  ⟨_,contact_old_at B u s target e rootGeom here⟩


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

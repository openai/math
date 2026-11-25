import OAI.Hierarchy.DescentContactSenderMass
import OAI.Hierarchy.DescentContactDonorReached
import OAI.Hierarchy.DescentResetPublicDonorRead
import OAI.Hierarchy.DescentResetContactShapePayload
import OAI.Hierarchy.DescentFallbackOperandRead

namespace OAI
/-! # The multiplicity on a directed socket is the true granular width of its contact -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentSharedCableNames DescentIssuedFallbackPanel DescentPlainTerminal
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOldContactSender DescentGroupPeerOrder
open DescentContacts DescentDenseHostOrder DescentResetAttachments DescentStageEdgeReceipt DescentHostDirectory
open DescentContactDonorFront DescentContactPreROM DescentOldSenderReturn DescentResetOppositePayload
open DescentContactSenderMass DescentResetLocalRoster
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "A" => input.placement
local notation "m" => S.groupWidth k tail i+k
local notation "c" => (T).commonDepth
local notation "L" => 2^(m-c)
local notation "K" => 2*(A).cap
local notation "native" => input.order.trans Fin.valEmbedding
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "basis" => B.frame.basis
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation:max "center" s:arg a:arg => ((Z).rootVertex T ((R).owner s a),(Z).rootBlock T ((R).owner s a))
local notation:max "senderId" s:arg a:arg => (Z).senderJoint T s a
local notation:max "offset" side:arg e:arg => localAddress («c»:=c) (A) native S input.valid words basis side (beforeStem B e)

/-- Recovering the address from a previous grain proves that the signed list has no
duplicate donor for that grain. The low block is recovered by quotient/remainder on the chosen basis. -/
theorem originalDonor_row {u : Host} {side : Bool} {j : Fin (L*K)} {e : (old).graph.Edge}
    (hit : originalDonor B u side j=some e) : j=finProdFinEquiv (offset side e) := by
  obtain ⟨⟨lo,z⟩,rfl⟩:=(@finProdFinEquiv L K).surjective j
  rw [original_query] at hit
  obtain ⟨grain,atOld,real⟩:=Option.map_eq_some_iff.mp hit
  obtain rfl : (priorGrain B).symm grain=e:=real
  have back : beforeStem B ((priorGrain B).symm grain)=grain:=(priorGrain B).apply_symm_apply grain
  rw [back]
  let v:=B.frame.host.symm (receiverRoot B u).1
  let hi:=(receiverRoot B u).2
  have located : DescentIssuedFallbackPanel.address (A) native S input.valid (port (A) side grain)=(donor words basis small v hi lo,z):=by
    apply (atSlot_iff (A) native S input.valid ..).mp
    simpa only [localQuery,Equiv.symm_apply_apply] using atOld
  change finProdFinEquiv _=finProdFinEquiv (subcell words basis _,_)
  rw [located]
  apply congrArg finProdFinEquiv
  refine Prod.ext ?_ rfl
  change lo=DescentPlainTerminal.low (rearrange basis ((words).symm ((donor words basis small v hi lo).1.1,
    (donor words basis small v hi lo).2)))
  simp [donor]

variable {b : ℕ} (u : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k) (s : Bool) (a : B.reset.placement.Contact)
variable (atRoot : receiverRoot B u=(B.reset.rootVertex B.terminals (B.reset.placement.owner s a), B.reset.rootBlock B.terminals (B.reset.placement.owner s a)))
variable (labels : Fin ((2^(S.groupWidth k tail i+k-B.terminals.commonDepth))*(2*input.placement.cap))→Cell b)
variable (read : ∀j,(labels j).val=(originalDonor B u s j).elim 0 (fun e=>B.reset.senderJoint B.terminals s (B.reset.placement.contact e)))

include atRoot read in
theorem contact_exact_donor (j : Fin (L*K)) :
    (labels j).val=senderId s a ↔ ∃e,originalDonor B u s j=some e ∧ (R).contact e=a := by
  cases found : originalDonor B u s j with
  | none=>simp [read,found,Ne.symm (sender_not_zero B s a)]
  | some e=>
    have geo:=(contact_old_slot_location B u s (finProdFinEquiv.symm j) e found).symm.trans atRoot
    simp only [read,found,Option.elim_some,Option.some.injEq,exists_eq_left']
    exact ⟨contact_sender_word_unique B s (congrArg Prod.fst geo) (congrArg Prod.snd geo),congrArg ((Z).senderJoint T s)⟩

include atRoot read in
theorem contact_mass_from_labels :
    price (senderId s a) labels=(blocks B).count (contactParent B a) := by
  have positive : 0<(Z).unit:=by rw [B.unit,←B.next.grain];exact Nat.mul_pos B.next.placement.unitPos G.base_pos
  rw [(contact_units B a positive).1]
  let F₀:={j : Fin (L*K) // (labels j).val=senderId s a}
  let E₀:={e : (old).graph.Edge // (R).contact e=a}
  have get (j : F₀) : ∃e,originalDonor B u s j.val=some e ∧ (R).contact e=a:=
    (contact_exact_donor B u s a atRoot labels read j.val).1 j.property
  let decode : F₀→E₀:=fun j=>⟨(get j).choose,(get j).choose_spec.2⟩
  apply Fintype.card_congr (Equiv.ofBijective decode ?_)
  constructor
  · intro x y eqn
    have same:=(congrArg Subtype.val eqn : (decode x).val=(decode y).val)
    apply Subtype.ext
    exact (originalDonor_row B (get x).choose_spec.1).trans
      ((congrArg (fun e=>finProdFinEquiv (offset s e)) same).trans (originalDonor_row B (get y).choose_spec.1).symm)
  · intro e
    obtain ⟨j,atOld⟩:=originalDonor_exists B u s a atRoot e.val (congrArg ((R).owner s) e.property)
    let p : F₀:=⟨j,(contact_exact_donor B u s a atRoot labels read j).2 ⟨e.val,atOld,e.property⟩⟩
    refine ⟨p,Subtype.ext ?_⟩
    exact Option.some.inj ((get p).choose_spec.1.symm.trans atOld)

variable (H M field query cargo base : ℕ) (pad : Fintype.card input.V≤H)
local notation "X" => donorFront B H M field query cargo
local notation "A₀" => (X).sender base
local notation "Y" => 2^(Z).n
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "N" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
local notation "origin" => input.vertex.trans (Fin.castLEEmb pad)
local notation:max "oldActor" u:arg => B.frame.host.symm (receiverRoot B u).1
local notation:max "lane" u:arg => (receiverRoot B u).2
local notation "oldCells" => Fin H→Block c→Fin N→Cell field
variable (setup : (senderDesk B field).Inputs) (xs : Fin H→Block B.terminals.commonDepth→Fin (DescentOldContactSender.count input.placement.degree (2^(S.groupWidth k tail i+k-B.terminals.commonDepth)) input.placement.cap B.reset.n (B.reset.k-B.terminals.commonDepth))→Cell field)
variable (measured : ∀v hi,decode (xs ((input.vertex.trans (Fin.castLEEmb pad)) v) hi)=(senderDesk B field).sample setup v hi)
local notation "locals" => fun side (j : Fin (L*K))=> (A₀).sentValue xs side (finProdFinEquiv.symm j) 0

include measured in
theorem mass_labels (u : Host) s (j : Fin (L*K)) :
    (locals s j (origin (oldActor u)) (lane u)).val=(originalDonor B u s j).elim 0 (fun e=>senderId s ((R).contact e)) := by
  let x := fun (h : Fin (Fintype.card input.V)) => xs (Fin.castLEEmb pad h)
  have reads := reached_old_senders B setup x (fun a hi => measured a hi)
  have seen := old_label_at B _ reads u s j 0
  change (point Ht s (decode (xs (origin (oldActor u)) (lane u))) (finProdFinEquiv.symm j)
    (Fin.castLE (by decide : 2≤3) (0 : Fin 2)) : Cell field).val = _ at seen
  have zero : Fin.castLE (by decide : 2≤3) (0 : Fin 2) = 0 := rfl
  rw [zero] at seen
  change (point Ht s (decode (xs (origin (oldActor u)) (lane u))) (finProdFinEquiv.symm j) 0 : Cell field).val = _
  cases hit : originalDonor B u s j <;>
    simpa only [hit, Option.elim_none, Option.elim_some, senderWords, Matrix.cons_val_zero] using seen

include measured in
theorem paid_contact_mass (u : Host) (j : Fin (contactCount B)) (a : (R).Contact)
    (root : receiverRoot B u=center (donor_query B j).1 a) (named : (donor_query B j).2=senderId (donor_query B j).1 a)
    (wide : L*K<2^field) :
    (Date.values A₀ locals j (origin (oldActor u)) (lane u)).val=(blocks B).count (contactParent B a) := by
  let s:=(donor_query B j).1
  let row:=fun i=>locals s i (origin (oldActor u)) (lane u)
  change ((price (donor_query B j).2 row:Cell field)).val=_
  rw [Fin.val_cast_of_lt ((bounded _ row).trans_lt wide),named]
  exact contact_mass_from_labels B u s a root row (mass_labels B H M field query cargo base pad setup xs measured u s)

include measured in
/-- A nonempty mass word itself certifies that the earlier signed panel carried a donor
for this socket. No installed positive edge or separately supplied presence flag is needed. -/
theorem positive_contact_mass (u : Host) (j : Fin (contactCount B))
    (positive : 0<(Date.values A₀ locals j (origin (oldActor u)) (lane u)).val) :
    ∃a : (R).Contact,receiverRoot B u=center (donor_query B j).1 a ∧
      (donor_query B j).2=senderId (donor_query B j).1 a ∧ 0<(blocks B).count (contactParent B a) := by
  let s:=(donor_query B j).1
  let row:=fun i=>locals s i (origin (oldActor u)) (lane u)
  let amt:=price (donor_query B j).2 row
  have ne : amt≠0:=by intro eqn;change 0<(amt:Cell field).val at positive;rw [eqn] at positive;exact (Nat.lt_irrefl _ positive)
  obtain ⟨i,hit⟩:=Classical.choice (Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero ne))
  have stored:=mass_labels B H M field query cargo base pad setup xs measured u s i
  have pos : 0<(donor_query B j).2:=Nat.succ_pos _
  cases found : originalDonor B u s i with
  | none=>rw [found,Option.elim_none] at stored;exact False.elim ((Nat.ne_of_gt pos) (hit.symm.trans stored))
  | some e=>
    rw [found,Option.elim_some] at stored
    let a:=(R).contact e
    have actual:=(contact_old_slot_location B u s (finProdFinEquiv.symm i) e found)
    have named:=hit.symm.trans stored
    have count:=contact_mass_from_labels B u s a actual row (mass_labels B H M field query cargo base pad setup xs measured u s)
    exact ⟨a,actual,named,by rw [←count,←named];exact Nat.pos_of_ne_zero ne⟩

theorem query_injective : Function.Injective (donor_query B) := by
  intro a d same
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · exact finTwoEquiv.injective (congrArg Prod.fst same)
  · apply Fin.ext
    exact Nat.add_right_cancel (congrArg Prod.snd same)

local notation:max "mass" u:arg j:arg => (Date.values A₀ locals j (origin (oldActor u)) (lane u)).val

include measured in
theorem mass_selected (u : Host) (j : Fin (contactCount B)) (x) (found : localOrigin B u (contactShelfIndex B j)=some x)
    (wide : L*K<2^field) : mass u j=(blocks B).count x.val ∧
      (if (donor_query B j).1 then (blocks B).dst x.val else (blocks B).src x.val)=u := by
  obtain ⟨a,alive,eqn,key⟩:=(contact_shelf_iff B u j x).1 found
  have before:=donor_query_actual B u a alive
  rw [key] at before
  have dst:=congrArg Prod.fst before
  have name:=congrArg Prod.snd before
  have root:=contact_at_root B (u:=u) ⟨a,alive.2⟩
  have atRoot : receiverRoot B u=center (donor_query B j).1 a:=by rw [dst];exact root
  have named : (donor_query B j).2=senderId (donor_query B j).1 a:=by rw [dst];exact name
  have amt:=paid_contact_mass B H M field query cargo base pad setup xs measured u j a atRoot named wide
  rw [eqn]
  refine ⟨amt,?_⟩
  rw [dst]
  by_cases l : (blocks B).src (contactParent B a)=u
  · simp [l]
  · simpa [l] using alive.2.resolve_left l

include measured in
theorem oriented_mass_live (u : Host) (j : Fin (contactCount B)) (amount : 0< mass u j) :
    ∃a : (R).Contact, receiverRoot B u=center (donor_query B j).1 a ∧ (donor_query B j).2=senderId (donor_query B j).1 a ∧
      ((if (donor_query B j).1 then (blocks B).dst (contactParent B a) else (blocks B).src (contactParent B a))=u →
        ∃x,localOrigin B u (contactShelfIndex B j)=some x ∧ x.val=contactParent B a) := by
  obtain ⟨a,atRoot,named,pos⟩:=positive_contact_mass B H M field query cargo base pad setup xs measured u j amount
  refine ⟨a,atRoot,named,?_⟩
  intro here
  let e:=contactParent B a
  have flag : decide ((blocks B).src e≠u)=(donor_query B j).1 := by
    cases eqn : (donor_query B j).1
    · simpa [eqn] using (show (blocks B).src e=u from by simpa [eqn] using here)
    · have dst : (blocks B).dst e=u:=by simpa [eqn] using here
      exact decide_eq_true (fun lhs=>contact_no_loop B a (lhs.trans dst.symm))
  have active : DescentResetLocalRoster.active (blocks B) u e := by
    refine ⟨pos,?_⟩
    cases eqn : (donor_query B j).1
    · exact Or.inl (by simpa [eqn] using here)
    · exact Or.inr (by simpa [eqn] using here)
  have address:=donor_query_actual B u a active
  rw [flag] at address
  have key : contactDigit B u ⟨a,active⟩=j:=query_injective B (address.trans (Prod.ext rfl named.symm))
  exact ⟨⟨e,active⟩,(contact_shelf_iff B u j _).2 ⟨a,active,rfl,key⟩,rfl⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

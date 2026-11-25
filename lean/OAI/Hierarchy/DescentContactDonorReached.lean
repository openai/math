import OAI.Hierarchy.DescentContactDonorMarkers
import OAI.Hierarchy.DescentContactPreROMRead
import OAI.Hierarchy.DescentOldSenderBook

namespace OAI
/-! # The attained donor-to-marker transaction supplies the complete physical contact sheet -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentSharedCableNames DescentIssuedFallbackPanel DescentPlainTerminal
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOldContactSender DescentGroupPeerOrder
open DescentContacts DescentDenseHostOrder DescentResetAttachments DescentStageEdgeReceipt DescentHostDirectory
open DescentPacking.PackedMatch.Local.Stage DescentContactDonorFront DescentContactPreROM DescentOldSenderReturn DescentResetOppositePayload
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "r" => (Z).k-(T).commonDepth
local notation "height" => GroupStage.depthBound D n f g
local notation "seat" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "R" => (Z).placement
local notation "native" => input.order.trans Fin.valEmbedding
local notation "gr" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "basis" => B.frame.basis
local notation "E" => W.granular B.count (z*G.b) B.fit
local notation "oldV" => fun u => B.frame.host.symm (receiverRoot B u).1
local notation "oldG" => fun u => (receiverRoot B u).2

def donorFront (H M field query cargo : ℕ) : Shape :=
  ⟨H,J,M,(A).degree,L,(A).cap,(Z).n,r,height,field,query,cargo⟩

variable (H M field query cargo base width : ℕ) (pad : Fintype.card input.V≤H)
local notation "X" => donorFront B H M field query cargo
local notation "S₀" => (X).sender base
local notation "C₀" => (X).markers base seat width
local notation "N" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
local notation "host" => input.vertex.trans (Fin.castLEEmb pad)
local notation "names" => cableNames k (groupRank ((gr).trans Fin.valEmbedding) ((host).trans Fin.valEmbedding))
local notation "adj" => hostRotor host (hostRoster (A) ((host).trans Fin.valEmbedding))
local notation "rank" => (Z).rawHostRank T (B.frame.host.symm.toEmbedding.trans host)
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "lane" => Block (T).commonDepth
local notation "oldCells" => Fin H→lane→Fin N→Cell field
local notation "marks" => Fin L→Fin K→Fin H→lane→Cell field
local notation "grid" => Fin H→Fin (A).degree→Option (Fin H)
variable (xs : Fin H → Block B.terminals.commonDepth → Fin (DescentOldContactSender.count input.placement.degree (2^(S.groupWidth k tail i+k-B.terminals.commonDepth)) input.placement.cap B.reset.n (B.reset.k-B.terminals.commonDepth)) → Cell field)
  (next : Fin H → Fin input.placement.degree → Option (Fin H))
  (raw : Fin (2^(S.groupWidth k tail i+k-B.terminals.commonDepth)) → Fin (2*input.placement.cap) → Fin H → Block B.terminals.commonDepth → Cell field)
local notation "label" => (S₀).sentValue xs
local notation "back" => (S₀).arrivedValue xs next raw
local notation "src" => (X).sensorValue base xs next raw
local notation "ys" => (X).boardValues xs
local notation "local5" => fun (v : Fin (H*seat)) (l : lane) (s : Bool) (j : Fin (L*K)) (a : Fin 5)=>
  DescentContactProbePitch.lift (S:=seat) (src s j a) v l
local notation "pair2" => fun (v : Fin (H*seat)) (l : lane) (s : Bool) (j : Fin (L*K)) (a : Fin 2)=>
  DescentContactProbePitch.lift (S:=seat) ((C₀).viewValue ys ((C₀).view s j a)) v l
local notation "root" => contactReceiver B
local notation "phys" => finProdFinEquiv.symm
variable (setup : (senderDesk B field).Inputs)
variable (measured : ∀v l,decode (xs ((input.vertex.trans (Fin.castLEEmb pad)) v) l)=(senderDesk B field).sample setup v l)
variable (ports : ∀v j, next ((input.vertex.trans (Fin.castLEEmb pad)) v) j = (hostRoster input.placement (input.vertex.trans Fin.valEmbedding) v j).map (input.vertex.trans (Fin.castLEEmb pad)))
variable (signed : ∀v l lo j, raw lo j ((input.vertex.trans (Fin.castLEEmb pad)) v) l = DescentResetOppositePayload.widened input.placement.degree input.placement.cap field
  (Stage.signedPanel input.placement (input.order.trans Fin.valEmbedding) S input.valid (cableNames k (groupRank ((Function.Embedding.refl (Fin (S.groupCount i))).trans Fin.valEmbedding) ((input.vertex.trans (Fin.castLEEmb pad)).trans Fin.valEmbedding)))
    (donor (S.resetInputDigits ctl.base ctl.radix i) B.frame.basis (B.frame.enough.trans (Nat.sub_le ..)) v l lo) j))
variable (coded : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤field) (positive : 0<field)

theorem actor_field (v : B.next.V) (l : lane) :
    DescentContactProbePitch.owner (rank v)=host (oldV (root v l)) ∧ oldG (root v l)=l := by
  constructor
  · change (finProdFinEquiv.symm (finProdFinEquiv ((Z).hostFields T _ v))).1=_
    rw [Equiv.symm_apply_apply];rfl
  · change (S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth).symm
      ((S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth) l)=l
    exact Equiv.symm_apply_apply _ _

include ports signed in
private theorem moved (s : Bool) (v : input.V) (l : lane) (t : Fin L×Fin K) (f : Fin 2) :
    back s t f (host v) l=returned (A) native S input.valid gr host words basis small
      (fun z h hi lo=>label (!s) (lo,z) (Fin.castLE (by decide) f) h hi) s t.1 t.2 (host v) l := by
  have env (u : input.V) (i : Fin (A).degree) : next (host u) i=adj (host u) i:=
    (ports u i).trans (host_at (A) host u i).symm
  have srcAt (u : input.V) (z : Fin K) : raw t.1 z (host u) l=
      previousSigned (b:=field) (A) native S input.valid gr host words basis small t.1 z (host u) l :=
    (signed u l t.1 z).trans (previous_signed_at (b:=field) (A) native S input.valid gr host words basis small u l t.1 z).symm
  have gate (a z : Fin (A).degree) : DescentResetReciprocalPeer.reaches next (host v) a z ↔
      DescentResetReciprocalPeer.reaches adj (host v) a z:=by
    unfold DescentResetReciprocalPeer.reaches
    rw [env,host_at (A) host]
    cases go : hostRoster (A) ((host).trans Fin.valEmbedding) v a with
    | none=>rfl
    | some u=>simp only [Option.map_some,Option.bind_some,env]
  let real := previousSigned (b:=field) (A) native S input.valid gr host words basis small t.1
  let cargoAt := fun z h hi => label (!s) (t.1,z) (Fin.castLE (by decide) f) h hi
  change both (A).degree (A).cap field (!s)
      (DescentResetOppositePayload.digits (cap:=(A).cap) next (raw t.1 t.2) (raw t.1) cargoAt (host v) l) =
    both (A).degree (A).cap field (!s)
      (DescentResetOppositePayload.digits (cap:=(A).cap) adj (real t.2) real cargoAt (host v) l)
  unfold DescentResetOppositePayload.digits
  apply congrArg (both (A).degree (A).cap field (!s))
  rw [srcAt]
  congr 1
  · funext j
    rw [env,host_at (A) host]
    cases edge : hostRoster (A) ((host).trans Fin.valEmbedding) v j.1 with
    | none=>rfl
    | some u=>exact srcAt u j.2
  · funext j;rw [env]
  · funext a z;rw [propext (gate a z)]

include measured in
private theorem first_read (v : B.next.V) (l : lane) (s : Bool) (j : Fin (L*K)) (bit : Fin 2) :
    (label s (phys j) (Fin.castLE (by decide) bit) (host (oldV (root v l))) l).val =
      (originalDonor B (root v l) s j).elim 0 (fun e=>senderWords B s e bit) := by
  let x := fun (h : Fin (Fintype.card input.V)) => xs (Fin.castLEEmb pad h)
  have reads := reached_old_senders B setup x (fun a hi => measured a hi)
  have seen := old_label_at B _ reads (root v l) s j bit
  have atLane := (actor_field B H pad v l).2
  change (point height s (decode (xs (host (oldV (root v l))) (oldG (root v l)))) (phys j) (Fin.castLE (by decide) bit) : Cell field).val = _ at seen
  have eqn := congrArg (fun hi => (point height s (decode (xs (host (oldV (root v l))) hi)) (phys j) (Fin.castLE (by decide) bit) : Cell field).val) atLane
  exact eqn.symm.trans seen

include measured ports signed coded positive in
theorem reached_donor_sensors (v : B.next.V) (l : lane) :
    ContactSensors B (root v l) (local5 (rank v) l) (pair2 (rank v) l) := by
  let u:=root v l
  let actor:=oldV u
  have geo:=actor_field B H pad v l
  have atHost : DescentContactProbePitch.owner (rank v)=host actor:=geo.1
  have atLane : oldG u=l:=geo.2
  have actual (s : Bool) (j : Fin (L*K)) :
      originalDonor B u s j=(atSlot (A) native S input.valid s
        (donor words basis small actor l (phys j).1) (phys j).2).map (priorGrain B).symm := by
    rw [original_query]
    change (atSlot _ _ _ _ _ (donor _ _ _ _ (oldG u) _) _).map _=_
    rw [atLane]
  have first := first_read B H M field query cargo base pad xs setup measured v l
  constructor
  · intro s j
    change (label s (phys j) 0 (DescentContactProbePitch.owner (rank v)) l).val=_
    exact (congrArg (fun h : Fin H => (label s (phys j) 0 h l).val) atHost).trans (first s j 0)
  · intro s j e found
    let t:=phys j
    have orig := found
    rw [actual] at found
    obtain ⟨p,hit,eqn⟩:=Option.map_eq_some_iff.mp found
    obtain rfl : (priorGrain B).symm p=e:=eqn
    let far:=port (A) (!s) p
    let y:=rearrange basis (oldBlock words far.1)
    let atFar:=DescentIssuedFallbackPanel.address (A) native S input.valid far
    let endId:=(priorGrain B).symm p
    have remote (bit : Fin 2) : (back s t bit (host actor) l).val=senderWords B (!s) endId bit := by
      have fromHere := moved B H M field query cargo base pad xs next raw ports signed s actor l t bit
      have got:=returned_at (A) native S input.valid gr host words basis small coded positive
        (fun z h hi lo=>label (!s) (lo,z) (Fin.castLE (by decide) bit) h hi) s actor l t.1 t.2 p hit
      refine (congrArg Fin.val (fromHere.trans got)).trans ?_
      have physical:=(senderDesk B field).read setup (!s) bit far.1.1.2 (high small y) (low y) atFar.2
      rw [opposite_slot (A) native S input.valid words basis small s p,Option.elim_some] at physical
      exact (congrArg (fun row => (point height (!s) row (low y,atFar.2) (Fin.castLE (by decide) bit) : Cell field).val)
        (measured far.1.1.2 (high small y))).trans physical
    have near:=first s j 1
    change (label s t 1 (host actor) l).val = (originalDonor B u s j).elim 0 (fun e => senderWords B s e 1) at near
    rw [orig,Option.elim_some] at near
    have survey:=(senderDesk B field).survey setup s actor l t.1 t.2 p hit
    have chip : (label s t 2 (host actor) l).val=(contactOldPort B s endId).val:=by
      change (point height s (decode (xs (host actor) l)) t 2:Cell field).val=_
      rw [measured]
      exact survey.1
    change (back s t 0 (DescentContactProbePitch.owner (rank v)) l).val=_ ∧ _ ∧
      (label s t 1 (DescentContactProbePitch.owner (rank v)) l).val=_ ∧
      (back s t 1 (DescentContactProbePitch.owner (rank v)) l).val=_ ∧
      (label s t 2 (DescentContactProbePitch.owner (rank v)) l).val=_
    have backAt (bit : Fin 2) := congrArg (fun h : Fin H => (back s t bit h l).val) atHost
    have sourceAt (bit : Fin 3) := congrArg (fun h : Fin H => (label s t bit h l).val) atHost
    refine ⟨(backAt 0).trans (remote 0),?_,(sourceAt 1).trans near,(backAt 1).trans (remote 1),(sourceAt 2).trans chip⟩
    intro ticket selected
    have pair:=survey.2 ticket selected
    have atView (bit : Fin 2) : pair2 (rank v) l s j bit=
        DescentReservedProbeInputs.value (Z).n r s (decode (xs (host actor) l)).1 t bit:=by
      change (C₀).viewValue ys ((C₀).view s j bit) (DescentContactProbePitch.owner (rank v)) l=_
      exact (congrArg (fun h : Fin H => (C₀).viewValue ys ((C₀).view s j bit) h l) atHost).trans
        ((C₀).viewValue_read ys s j bit (host actor) l)
    rw [atView,atView,measured]
    exact pair


variable (U : DescentContactSenderDate.Prior (A).degree L (A).cap (Z).n r) {bw : ℕ}
variable (budget : (X).Space base U bw) (end_ : (C₀).endAddress<2^bw)
    (markerWidth : M*max (field*8) width≤bw/2) (senderRoom : (S₀).Packed bw)
    (boardWidth : M*max (field*(C₀).oldFields) (C₀).viewBits≤bw/2)
    (shapeRoom : seat≤2^field) (markRoom : (A).degree*seat<2^width)
local notation "stage" => (X).result base seat width U (Z).graph budget end_ markerWidth
local notation "mem₀" => (X).memory base U
local notation "space₀" => (X).markerSpace base seat width U budget end_ markerWidth
local notation "entry" => issuedContactExpr B ((X).endAddress base) H M field width
local notation "value" => issuedContactValue B ((X).endAddress base) H M field width local5 pair2
local notation "rawHost" => Fin (H*seat)

include pad measured ports signed coded positive senderRoom boardWidth shapeRoom markRoom in
/-- A single native memory is advanced from the old measured board through the reciprocal
sender exchange to the raw-actor contact predicate. All seven marker inputs are derived. -/
theorem reached_contact_period (mem : Memory bw) (inputRows : (S₀).Before U xs next raw mem) :
    ((X).period base seat width U (Z).graph budget end_ markerWidth).Exec mem (stage mem)
      ((X).clock base seat width U (Z).graph budget end_ markerWidth) ∧
    CheapCode ((X).period base seat width U (Z).graph budget end_ markerWidth) ∧
    (∀key donor chunk v,(entry key donor chunk).eval (stage mem) (v.val:Word bw)=
      ((data (M:=M) (value key donor) (v,chunk)).val:Word bw)) ∧
    (∀(v : B.next.V) (x : rawHost),
      (∃key donor,rowHit B next (rank v) x (value key donor)) ↔
        ∃c : (R).Contact,rawPeer B (contactParent B c) (rank v).val x.val) ∧
    ∀addr,addr<base ∨ (C₀).endAddress≤addr→stage mem addr=mem addr := by
  obtain ⟨go,cheap,frame⟩:=(X).period_any base seat width U (Z).graph budget end_ markerWidth mem
  have sensors:=reached_donor_sensors B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
  have earlier (a : ℕ) (h : a<base) : mem₀ mem a=mem a:=((X).any base U budget mem).2.2 a (.inl h)
  have board (j : Fin (C₀).oldFields) : Source ((X).oldBoard U j) (fun h l=>ys h l j) M (mem₀ mem):=fun p=>
    (eval_below _ _ _ _ (budget.sender.board _) earlier).trans (inputRows.input _ p)
  have all:=(X).sources base U budget xs next raw mem senderRoom inputRows
  refine ⟨go,cheap,?_,?_,frame⟩
  · exact issued_contact_rows B ((X).endAddress base) H M field width ((X).oldBoard U) ((X).priorSensor base)
      space₀ (mem₀ mem) ys src senderRoom.positive boardWidth board all
  · exact issued_contact_tickets B ((X).endAddress base) H M field width pad local5 pair2 sensors shapeRoom markRoom next ports

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

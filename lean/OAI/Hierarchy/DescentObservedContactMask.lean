import OAI.Hierarchy.DescentPhysicalContactMeta
import OAI.Hierarchy.DescentResetOriginalFees

namespace OAI
/-! # Four attained contact fields and their native per-receiver comparison -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentSharedCableNames DescentIssuedFallbackPanel DescentPlainTerminal
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOldContactSender DescentGroupPeerOrder
open DescentContacts DescentDenseHostOrder DescentResetAttachments DescentStageEdgeReceipt DescentHostDirectory
open DescentContactOutputShape DescentResetOriginHaloRAM DescentResetSignedHaloMatrix DescentSortedRoster
open DescentPacking.PackedMatch.Local.Stage DescentContactDonorFront DescentContactPreROM DescentOldSenderReturn DescentResetOppositePayload
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
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
local notation:max "oldV" u:arg => B.frame.host.symm (receiverRoot B u).1
local notation:max "oldG" u:arg => (receiverRoot B u).2

variable (H M field query cargo base width : ℕ) (pad : Fintype.card input.V≤H)
local notation "X" => donorFront B H M field query cargo
local notation "S₀" => (X).sender base
local notation "C₀" => (X).markers base seat width
local notation "N" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
local notation "host" => input.vertex.trans (Fin.castLEEmb pad)
local notation "names" => cableNames k (groupRank ((gr).trans Fin.valEmbedding) ((host).trans Fin.valEmbedding))
local notation "adj" => hostRotor host (hostRoster (A) ((host).trans Fin.valEmbedding))
local notation "rank" => (Z).rawHostRank T (B.frame.host.symm.toEmbedding.trans host)
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "lane" => Block (T).commonDepth
local notation "oldCells" => Fin H→lane→Fin N→Cell field
local notation "marks" => Fin L→Fin K→Fin H→lane→Cell field
local notation "grid" => Fin H→Fin (A).degree→Option (Fin H)
variable (xs : oldCells) (next : grid) (raw : marks)
local notation "label" => (S₀).sentValue xs
local notation "back" => (S₀).arrivedValue xs next raw
local notation "src" => (X).sensorValue base xs next raw
local notation "ys" => (X).boardValues xs
local notation "local5" => fun (v : Fin (H*seat)) (l : lane) (s : Bool) (j : Fin (L*K)) (a : Fin 5)=>
  DescentContactProbePitch.lift (S:=seat) (src s j a) v l
local notation "pair2" => fun (v : Fin (H*seat)) (l : lane) (s : Bool) (j : Fin (L*K)) (a : Fin 2)=>
  DescentContactProbePitch.lift (S:=seat) ((C₀).viewValue ys ((C₀).view s j a)) v l
local notation:max "root" v:arg l:arg => contactReceiver B v l
local notation "phys" => finProdFinEquiv.symm
variable (setup : (senderDesk B field).Inputs)
variable (measured : ∀v l,decode (xs (host v) l)=(senderDesk B field).sample setup v l)
variable (ports : ∀v j,next (host v) j=(hostRoster (A) (input.vertex.trans Fin.valEmbedding) v j).map host)
variable (signed : ∀v l lo j,raw lo j (host v) l=DescentResetOppositePayload.widened (A).degree (A).cap field
  (Stage.signedPanel (A) native S input.valid names (donor words basis small v l lo) j))
variable (coded : DescentSignedCableCodec.width (A).degree (A).cap≤field) (positive : 0<field)

local notation "groups" => S.groupCount (i+1)
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation:max "center" s:arg a:arg => ((Z).rootVertex T ((R).owner s a),(Z).rootBlock T ((R).owner s a))
local notation:max "atSide" s:arg a:arg => (if s then (blocks B).dst (contactParent B a) else (blocks B).src (contactParent B a))
variable (batch «meta» : ℕ)
local notation "Y" => contactOutputs B H M field query cargo groups (2^k) batch width «meta»
local notation "cells" => (Y).rawIndicators base (Z).graph xs next raw
local notation "rad" => 2^(Nat.clog 2 ((A).degree+2))
local notation:max "short_" p:arg v:arg => short (b:=cargo) p id (host v)

local notation:max "site_" v:arg groupIx:arg x:arg => (((groupIx,v),x) : Host)
local notation:max "read_" t:arg registerIx:arg v:arg groupIx:arg x:arg => ((cells t).indicators.output registerIx (rank v) ((digits).symm (groupIx,x))).val
variable (keys : DescentResetLocalRoster.rootSlots r (2^(Z).n)*(2^(Z).n+2^height)<2^field)
    (halo : (A).degree+2<2^cargo) (coord : seat*rad≤2^«meta»)
open DescentParallelBase
private theorem contact_size (a : (R).Contact) :
    (blocks B).count (contactParent B a)≤B.next.placement.cap:=by
  let e:=contactParent B a
  by_cases paid : 0<(blocks B).count e
  · let u:=(blocks B).src e
    let l : Local (blocks B) u:=⟨e,paid,Or.inl rfl⟩
    exact (Finset.single_le_sum (f:=fun a : Local (blocks B) u=>(blocks B).count a.val)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ l)).trans (local_count_le B u)
  · exact (Nat.eq_zero_of_not_pos paid).le.trans (Nat.zero_le _)

include measured ports signed coded positive keys halo coord in
theorem observed_live_fields (oldWord : L*K<2^field) (newWord : B.next.placement.cap<2^«meta»)
    (fieldRoom : seat≤2^field) (tagRoom : (A).degree*seat<2^width) (portRoom : (A).degree+1<2^query)
    (v : B.next.V) (groupIx : Fin groups) (x : Block k) (t : Fin (contactCount B))
    (a : (R).Contact) (s : Bool) (own : receiverRoot B (site_ v groupIx x)=center s a)
    (named : donor_query B t=(s,(Z).senderJoint T s a)) (paid : 0<(blocks B).count (contactParent B a)) (f₀ : Fin 4) :
    let h:=site_ v groupIx x
    let qualifies:=relativeShape B (atSide s a)=relativeShape B h
    let endpoint:=fun end_=>jointNumber B h (center end_ a).1 (relativeShape B (atSide end_ a))
    read_ t f₀ v groupIx x=
      (![ (blocks B).count (contactParent B a),if qualifies then endpoint false else 0,
        if qualifies then endpoint true else 0,jointNumber B h (receiverRoot B h).1 (relativeShape B h)] : Fin 4→ℕ) f₀ := by
  intro h qualifies endpoint
  let l:=(digits).symm (groupIx,x)
  have here : root v l=h:=reached_contact_receiver B v groupIx x
  have roots : receiverRoot B (root v l)=center s a:=by rw [here];exact own
  have branches:=reached_selected_operand B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch «meta» v l t s a roots named paid fieldRoom tagRoom portRoom halo keys coord
  have side : (donor_query B t).1=s:=congrArg Prod.fst named
  have name : (donor_query B t).2=(Z).senderJoint T (donor_query B t).1 a :=by rw [side];exact congrArg Prod.snd named
  have pos : receiverRoot B h=center (donor_query B t).1 a:=by rw [side];exact own
  have physicalValue:=(paid_contact_mass B H M field query cargo base pad setup xs measured h t a pos name oldWord)
  have geo:=actor_field B H pad v l
  have money : ((cells t).mass (rank v) l).val=(blocks B).count (contactParent B a):=by
    change (DescentContactMaskShape.realAmount (X) base xs t (DescentContactProbePitch.owner (rank v)) l).val=_
    refine (congrArg₂ (fun a b=>(DescentContactMaskShape.realAmount X base xs t a b).val) geo.1 geo.2.symm).trans ?_
    rw [here]
    exact physicalValue
  have quantity:=contact_size B a
  fin_cases f₀
  · change (DescentContactWidthPage.recode «meta» ((cells t).mass (rank v) l)).val=_
    rw [DescentContactWidthPage.recode,money,Fin.val_cast_of_lt (quantity.trans_lt newWord)]
    rfl
  · change ((cells t).indicators.selected (some false) (rank v) l).val = (if qualifies then endpoint false else 0)
    simpa only [here,qualifies,endpoint] using branches (some false)
  · change ((cells t).indicators.selected (some true) (rank v) l).val = (if qualifies then endpoint true else 0)
    simpa only [here,qualifies,endpoint] using branches (some true)
  · change ((cells t).indicators.selected none (rank v) l).val = jointNumber B h (receiverRoot B h).1 (relativeShape B h)
    simpa only [here] using branches none

local notation:max "oldMass" t:arg u:arg => (DescentContactMaskShape.realAmount X base xs t (host (oldV u)) (oldG u)).val

include measured in
theorem observed_grain_count (oldWord : L*K<2^field) (newWord : B.next.placement.cap<2^«meta»)
    (v : B.next.V) (groupIx : Fin groups) (x : Block k) (t : Fin (contactCount B)) :
    read_ t 0 v groupIx x=oldMass t (site_ v groupIx x) := by
  let u:=site_ v groupIx x
  let hi:=(digits).symm (groupIx,x)
  have same:=reached_contact_receiver B v groupIx x
  have geo:=actor_field B H pad v hi
  change (DescentContactWidthPage.recode «meta» (DescentContactMaskShape.realAmount X base xs t
    (DescentContactProbePitch.owner (rank v)) hi)).val=_
  refine (congrArg₂ (fun a b=>(DescentContactWidthPage.recode «meta»
    (DescentContactMaskShape.realAmount X base xs t a b)).val) geo.1 geo.2.symm).trans ?_
  rw [same]
  have bounded : oldMass t u≤B.next.placement.cap:=by
    by_cases positive : 0<oldMass t u
    · obtain ⟨a,owns,named,_⟩:=oriented_mass_live B H M field query cargo base pad setup xs measured u t positive
      have countAt : oldMass t u = (blocks B).count (contactParent B a) :=
        paid_contact_mass B H M field query cargo base pad setup xs measured u t a owns named oldWord
      exact countAt.le.trans (contact_size B a)
    · omega
  exact Fin.val_cast_of_lt (bounded.trans_lt newWord)

include measured ports signed coded positive keys halo coord in
theorem observed_rank_requests (oldWord : L*K<2^field) (newWord : B.next.placement.cap<2^«meta»)
    (fieldRoom : seat≤2^field) (tagRoom : (A).degree*seat<2^width) (portRoom : (A).degree+1<2^query)
    (v : B.next.V) (groupIx : Fin groups) (x : Block k) (t : Fin (contactCount B))
    (p : Local (blocks B) (site_ v groupIx x)) (live : localOrigin B (site_ v groupIx x) (contactShelfIndex B t)=some p) :
    let u:=site_ v groupIx x
    let left:=(blocks B).src p.val
    let right:=(blocks B).dst p.val
    (receiverRoot B left).1∈originDomain B u ∧ (receiverRoot B right).1∈originDomain B u ∧
    read_ t 1 v groupIx x=jointNumber B u (receiverRoot B left).1 (relativeShape B left) ∧
    read_ t 2 v groupIx x=jointNumber B u (receiverRoot B right).1 (relativeShape B right) ∧
    read_ t 3 v groupIx x=jointNumber B u (receiverRoot B u).1 (relativeShape B u):=by
  intro u left right
  obtain ⟨a,alive,edge,key⟩:=(contact_shelf_iff B u t p).1 live
  let sc:=(donor_query B t).1
  have before:=donor_query_actual B u a alive
  rw [key] at before
  have side:=congrArg Prod.fst before
  have atRoot : receiverRoot B u=center sc a:=by rw [show sc=(donor_query B t).1 from rfl,side];exact contact_at_root B (u:=u) ⟨a,alive.2⟩
  have named : donor_query B t=(sc,(Z).senderJoint T sc a):=Prod.ext rfl (by rw [show sc=(donor_query B t).1 from rfl,side];exact congrArg Prod.snd before)
  have ownAt := (mass_selected B H M field query cargo base pad setup xs measured u t p live oldWord).2
  rw [edge] at ownAt
  have qualifies : relativeShape B (atSide sc a)=relativeShape B u:=congrArg (relativeShape B) ownAt
  have rows_:=observed_live_fields B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch «meta» keys halo coord oldWord newWord fieldRoom tagRoom portRoom v groupIx x t a sc atRoot named alive.1
  obtain ⟨e,witnessEq⟩:=contact_witness B a alive.1
  obtain ⟨idx,liveAt⟩:=originalDonor_exists B u sc a atRoot e (congrArg ((R).owner sc) witnessEq)
  have oldAt (s : Bool) : (center s a).1∈originDomain B u:=by
    simpa only [witnessEq] using endpoint_mem B u sc e idx liveAt s
  have leftRoot : receiverRoot B left=center false a:=by
    change receiverRoot B ((blocks B).src p.val)=_
    rw [edge];exact contact_endpoint_root B a false
  have rightRoot : receiverRoot B right=center true a:=by
    change receiverRoot B ((blocks B).dst p.val)=_
    rw [edge];exact contact_endpoint_root B a true
  rw [leftRoot,rightRoot]
  refine ⟨oldAt false,oldAt true,?_,?_,?_⟩
  · simpa [left,u,edge,qualifies] using rows_ 1
  · simpa [right,u,edge,qualifies] using rows_ 2
  · simpa [u] using rows_ 3

def observedMask (t : Fin (contactCount B)) (v : B.next.V) (groupIx : Fin groups) (x : Block k) (ranks : Fin 3→Cell «meta») (own : Cell «meta») : Fin 9→Cell «meta» :=
  let d : Fin 4→Cell «meta»:=fun j=>(read_ t j v groupIx x : ℕ)
  ![d 0,d 1,d 2,d 3,ranks 0,ranks 1,ranks 2,own,d 0]
include measured ports signed coded positive keys halo coord in
theorem observed_contact_meta (oldWord : L*K<2^field) (newWord : B.next.placement.cap<2^«meta»)
    (fieldRoom : seat≤2^field) (tagRoom : (A).degree*seat<2^width) (portRoom : (A).degree+1<2^query)
    (v : B.next.V) (groupIx : Fin groups) (x : Block k) (t : Fin (contactCount B)) (ranks : Fin 3→Cell «meta») (self : Cell «meta»)
    (rankRead : ∀p,localOrigin B (site_ v groupIx x) (contactShelfIndex B t)=some p→
      (ranks 0).val=localClass B (site_ v groupIx x) ((blocks B).src p.val) ∧
      (ranks 1).val=localClass B (site_ v groupIx x) ((blocks B).dst p.val) ∧
      (ranks 2).val=localClass B (site_ v groupIx x) (site_ v groupIx x))
    (absent : self.val≠0 ↔ (site_ v groupIx x)∉Stage.near B.next.placement (site_ v groupIx x)) :
    let u:=site_ v groupIx x
    let actual:=observedMask B H M field query cargo base width pad xs next raw batch «meta» t v groupIx x ranks self
    DescentCandidateMaskRAM.render actual=DescentResetFieldAssembler.raw «meta» (Hierarchy.DescentSixParty.ClosedReset.Window.meta B u (localOrigin B u (contactShelfIndex B t))) := by
  intro u actual
  let s:=(donor_query B t).1
  have physicalValue (registerIx : Fin 4) : ((read_ t registerIx v groupIx x : ℕ):Cell «meta»).val=read_ t registerIx v groupIx x:=by
    exact Fin.val_cast_of_lt (Fin.isLt _)
  have countRead:=observed_grain_count B H M field query cargo base width pad xs next raw setup measured batch «meta» oldWord newWord v groupIx x t
  have money : (actual 8).val=oldMass t u:=(physicalValue 0).trans countRead
  apply contact_program_meta B H M field query cargo base pad setup xs measured u t actual (fun z=>Nat.ne_of_gt (money.symm ▸ z))
    money _ oldWord rankRead absent
  intro a countAt roots key
  have matched : donor_query B t=(s,(Z).senderJoint T s a):=Prod.ext rfl key
  have enough:=paid_contact_mass B H M field query cargo base pad setup xs measured u t a roots key oldWord
  have live : 0<(blocks B).count (contactParent B a):=by rw [←enough];exact countAt
  have actualFields:=observed_live_fields B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch «meta» keys halo coord oldWord newWord fieldRoom tagRoom portRoom v groupIx x t a s roots matched live
  have compare (registerIx) : (((read_ t registerIx v groupIx x:ℕ):Cell «meta»).val)=_ := (physicalValue registerIx).trans (actualFields registerIx)
  have sat : 0<jointNumber B u (receiverRoot B u).1 (relativeShape B u):=by
    unfold jointNumber DescentContactCoordinateJoint.number
    omega
  change (((read_ t 1 v groupIx x:ℕ):Cell «meta»).val=((read_ t 3 v groupIx x:ℕ):Cell «meta»).val ∨
    ((read_ t 2 v groupIx x:ℕ):Cell «meta»).val=((read_ t 3 v groupIx x:ℕ):Cell «meta»).val) ↔ _
  rw [compare 1,compare 2,compare 3,joint_endpoint B s a]
  simp only [Nat.add_left_inj]
  have coordinateRule (P : Prop) [Decidable P] (left right base : ℕ) (positive : 0 < base)
      (inRange : P → left = base ∨ right = base) :
      ((if P then left else 0) = base ∨ (if P then right else 0) = base) ↔ P := by
    by_cases hP : P
    · exact ⟨fun _ => hP, fun h => by simpa [hP] using inRange h⟩
    · simp [hP, Ne.symm (Nat.ne_of_gt positive)]
  apply coordinateRule (relativeShape B (atSide s a) = relativeShape B u) _ _ _ sat
  intro aligned
  have ownCoordinate : jointNumber B u (center s a).1 (relativeShape B (atSide s a)) =
      jointNumber B u (receiverRoot B u).1 (relativeShape B u) := by
    rw [(congrArg Prod.fst roots).symm,aligned]
  cases hside : s
  · exact Or.inl (by simpa only [hside] using ownCoordinate)
  · exact Or.inr (by simpa only [hside] using ownCoordinate)

open DescentResetLocalRoster
open DescentDatedAddressBook
local notation "used" => Fintype.card B.next.V
local notation "names₀" => compactActorName B pad
local notation "dense₀" => compactActorOrder B pad
local notation "size₀" => H*seat
variable {bw : ℕ} {date : PhysicalReset} {floor : ℕ} {I : date.DateInputs floor bw} {N₁ H₁ : ℕ} (lives : used≤H₁)
    (board : I.CandidateChannels) (name : Fin N₁→Fin I.masked.sparseHosts) (rankBase : ℕ)
    (banks : DescentResetPeerJointRAM.Sources) (priorMem : Memory bw)
local notation "co₀" => date.successor.contactShape
variable (rows₀ : Fin size₀→Fin 4→Option (Fin size₀))
    (fits₀ : DescentResetPeerJointRAM.Room banks rankBase H₁ size₀ H (A).degree bw)
    (stored₀ : DescentResetPeerJointRAM.Reads banks used names₀ (indexed rows₀) adj priorMem)
    (jointRoom : seat*DescentResetPeerJointRAM.radix (A).degree≤2^bw) (slotsRoom : 4≤2^I.masked.field)


include measured ports signed coded positive keys halo coord fits₀ stored₀ jointRoom slotsRoom in
set_option maxHeartbeats 800000 in
theorem observed_present_word (oldWord : L*K<2^field) (newWord : B.next.placement.cap<2^«meta»)
    (fieldRoom : seat≤2^field) (tagRoom : (A).degree*seat<2^width) (portRoom : (A).degree+1<2^query)
    (v : B.next.V) (groupIx : Fin groups) (x : Block k) (t : Fin (contactCount B))
    (job : ℕ) (x₀ : Fin (co₀).blocks) (t₀ : Fin (co₀).sockets) (h₀ : Fin I.masked.hosts) (g₀ : Fin I.masked.groups)
    (sector : date.successor.jobAt job=some (.inl (x₀,t₀)))
    (capture : ∀f₀ : Fin 4,(DescentResetDenseOperand.dense (H:=I.masked.hosts) name (board.contact x₀ t₀ f₀) h₀ g₀).val=
      ((cells t).indicators.output f₀ (rank v) ((digits).symm (groupIx,x))).val)
    (peers : present rows₀ (rank v)=(insert v (B.next.placement.near v)).map rank)
    (menu : ∀j,(board.peer j h₀ g₀).val=DescentResetPeerJointRAM.value H seat (A).degree adj used names₀ (indexed rows₀)
      ((dense₀ v).castLE lives) j)
    (near : Fin size₀→Fin 3→Option (Fin size₀))
    (self : (board.aux 2 h₀ g₀).val=DescentResetPeerJointPacked.Aux.value seat names₀ adj near ((dense₀ v).castLE lives) 2)
    (missing : (∀j,near (rank v) j≠some (rank v)) ↔ v∉B.next.placement.near v)
    (size : «meta»=I.masked.field) :
    DescentCandidateMaskRAM.render (board.maskValues name job h₀ g₀)=
      DescentResetFieldAssembler.raw I.masked.field (Hierarchy.DescentSixParty.ClosedReset.Window.meta B (site_ v groupIx x)
        (localOrigin B (site_ v groupIx x) (contactShelfIndex B t))) :=by
  subst «meta»
  let ranks (j : Fin 3) : Cell I.masked.field:=board.maskValues name job h₀ g₀ ⟨4+j.val,by omega⟩
  let own:=board.aux 2 h₀ g₀
  let reached:=observedMask B H M field query cargo base width pad xs next raw batch I.masked.field t v groupIx x ranks own
  let saved (j : Fin 4) : Cell I.masked.field :=
    (((((contactOutputs B H M field query cargo groups (2^k) batch width I.masked.field).rawIndicators base (Z).graph xs next raw t).indicators.output j (rank v) ((digits).symm (groupIx,x))).val : ℕ) : Cell I.masked.field)
  have source (j : Fin 4) :
      DescentResetDenseOperand.dense (H:=I.masked.hosts) name (board.contact x₀ t₀ j) h₀ g₀ = saved j :=
    Fin.ext ((capture j).trans (Fin.val_cast_of_lt (Fin.isLt _)).symm)
  have mass : board.work name job h₀ g₀ = saved 0 := by
    unfold PhysicalReset.DateInputs.CandidateChannels.work
    rw [sector]
    exact source 0
  have endRead (role : Fin 3) : board.endpoint name job role h₀ g₀ = saved ⟨role.val+1,by omega⟩ := by
    unfold PhysicalReset.DateInputs.CandidateChannels.endpoint
    rw [sector]
    exact source _
  have mark : (if (date.successor.jobAt job).isSome then board.aux 2 h₀ g₀ else 0) = own := by
    simp [sector,own]
  have same : board.maskValues name job h₀ g₀=reached:=by
    exact contactMaskFields (board.maskValues name job h₀ g₀) saved own
      mass (endRead 0) (endRead 1) (endRead 2) mark mass
  rw [same]
  have yes : ((dense₀ v).castLE lives).val<used:=(dense₀ v).isLt
  have atRank : names₀ ⟨_,yes⟩=rank v:=by change rank ((dense₀).symm ((dense₀) v))=_;simp
  have gate:=self.trans (DescentResetPeerJointPacked.Aux.raw_missing seat names₀ adj near
    ((dense₀ v).castLE lives) yes)
  rw [atRank] at gate
  have absent : own.val≠0 ↔ (site_ v groupIx x)∉DescentSharedCableNames.Stage.near B.next.placement (site_ v groupIx x):=by
    change (board.aux 2 h₀ g₀).val≠0 ↔ _
    rw [self_missing B _,gate]
    by_cases h:∀j,near (rank v) j≠some (rank v)
    · simp [h,missing.mp h]
    · simp [h,mt missing.mpr h]
  apply observed_contact_meta B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch I.masked.field keys halo coord oldWord newWord fieldRoom tagRoom portRoom v groupIx x t ranks own _ absent
  intro a found
  obtain ⟨old₀,old₁,left,right,here⟩:=observed_rank_requests B H M field query cargo base width pad xs next raw setup
    measured ports signed coded positive batch I.masked.field keys halo coord oldWord newWord fieldRoom tagRoom portRoom
    v groupIx x t a found
  have endpointAt (role : Fin 3) : board.endpoint name job role h₀ g₀ =
      DescentResetDenseOperand.dense (H:=I.masked.hosts) name (board.contact x₀ t₀ ⟨role.val+1,by omega⟩) h₀ g₀ := by
    unfold PhysicalReset.DateInputs.CandidateChannels.endpoint
    rw [sector]
  apply mask_ranks_local B pad lives board name rankBase banks priorMem rows₀ fits₀ stored₀ jointRoom slotsRoom (site_ v groupIx x) h₀ g₀ peers menu job a old₀ old₁
  · exact (congrArg Fin.val (endpointAt 0)).trans ((capture 1).trans left)
  · exact (congrArg Fin.val (endpointAt 1)).trans ((capture 2).trans right)
  · exact (congrArg Fin.val (endpointAt 2)).trans ((capture 3).trans here)


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

import OAI.Hierarchy.DescentContactSelectedJoint
import OAI.Hierarchy.DescentContactSparseSensors
import OAI.Hierarchy.DescentContactProgramVisible
import OAI.Hierarchy.DescentResetContactRightHalo

namespace OAI
/-! # The four true contact operands carried by the measured reset raster -/
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

local notation "groups" => S.groupCount (i+1)
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation:max "center" s:arg a:arg => ((Z).rootVertex T ((R).owner s a),(Z).rootBlock T ((R).owner s a))
local notation:max "atSide" s:arg a:arg => (if s then (blocks B).dst (contactParent B a) else (blocks B).src (contactParent B a))
variable (batch «meta» : ℕ)
local notation "Y" => contactOutputs B H M field query cargo groups (2^k) batch width «meta»
local notation "cells" => (Y).rawIndicators base (Z).graph xs next raw
local notation "rad" => 2^(Nat.clog 2 ((A).degree+2))
local notation:max "short_" p:arg v:arg => short (b:=cargo) p id (host v)

theorem contact_group_digits : J=groups*(2^k) := by
  rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix]

theorem original_contact_lane (g : Fin groups) (x : Block k) :
    Fin.cast (contact_group_digits B).symm (finProdFinEquiv (g,x))=(digits).symm (g,x) := by
  apply Fin.ext
  rfl

theorem reached_contact_receiver (v : B.next.V) (g : Fin groups) (x : Block k) :
    root v ((digits).symm (g,x))=((g,v),x) := by simp [contactReceiver]

include ports in
private theorem true_old_halo (v : input.V) : short_ next v=short_ adj v := by
  have row : closed next (host v)=closed adj (host v):=by
    funext j
    induction j using Fin.lastCases with
    | last=>simp [closed]
    | cast j=>simpa [closed] using (ports v j).trans (host_at (A) host v j).symm
  funext j
  simp only [short,DescentResetSignedHaloMatrix.rank,(host v).isLt,dite_eq_left,id_eq,Fin.eta,
    DescentSortedRoster.before,DescentSortedRoster.present,row]

include measured ports signed coded positive in
theorem reached_raw_contact (v : B.next.V) (l : lane) (q : Fin (contactCount B))
    (fieldRoom : seat≤2^field) (tagRoom : (A).degree*seat<2^width)
    (portRoom : (A).degree+1<2^query) (haloRoom : (A).degree+2<2^cargo) :
    let s:=(donor_query B q).1
    let u:=root v l
    (∀j,((cells q).own j (rank v) l).val=(originalDonor B u s j).elim 0 (fun e=>(Z).senderJoint T s ((R).contact e))) ∧
    (∀j,((cells q).marker j (rank v) l).val=contactSheet B u q (finProdFinEquiv (finTwoEquiv.symm s,j))) ∧
    ((cells q).shape (rank v) l).val=relativeShape B u ∧
    ∀j e,originalDonor B u s j=some e→∀end_,((cells q).halo end_ j (rank v) l).val=haloNumber B u (center end_ ((R).contact e)).1+1 := by
  intro s u
  let actor:=oldV u
  have geo:=actor_field B H pad v l
  have sensors:=reached_donor_sensors B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
  refine ⟨?_,?_,?_,?_⟩
  · exact (sensors v l).own s
  · intro j
    let p:=finProdFinEquiv (finTwoEquiv.symm s,j)
    have measured_:=issued_contact_mark B ((X).endAddress base) H M field width pad local5 pair2 sensors fieldRoom tagRoom q p v l
    have socket : (finProdFinEquiv.symm ((C₀).index q p)).1 = q :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (q,p))
    exact (congrArg (fun key => ((C₀).marker (Z).graph key
      ((C₀).values ys src ((C₀).index q p) (rank v) l)).val) socket).trans measured_
  · exact (DescentContactProbePitch.shape_val (H:=H) (S:=seat) (G:=J) fieldRoom (rank v) l).trans (by
      change (finProdFinEquiv.symm (finProdFinEquiv ((Z).hostFields T _ v))).2.val=_
      rw [Equiv.symm_apply_apply];rfl)
  · intro j e donor_ side
    let t:=phys j
    have oldChip : raw t.1 t.2 (host actor) l=previousSigned (b:=field) (A) native S input.valid gr host words basis small t.1 t.2 (host actor) (oldG u):=by
      have atCell := (signed actor l t.1 t.2).trans
        (previous_signed_at (b:=field) (A) native S input.valid gr host words basis small actor l t.1 t.2).symm
      exact atCell.trans (congrArg (fun high => previousSigned (b:=field) (A) native S input.valid gr host words basis small t.1 t.2 (host actor) high) geo.2.symm)
    have roster:=true_old_halo (input:=input) H cargo pad next ports actor
    change (DescentPackedChildNeighbor.SIMD.lookup (short (b:=cargo) next id (DescentContactProbePitch.owner (rank v)))
      (if side then Right.askedField (A).degree (A).cap field query
        (raw t.1 t.2 (DescentContactProbePitch.owner (rank v)) l) 0 else askedField (A).degree (A).cap field query
        (raw t.1 t.2 (DescentContactProbePitch.owner (rank v)) l) 0) _).val=_
    rw [geo.1,roster,oldChip]
    cases side
    · exact old_raw_halo_at B pad coded portRoom haloRoom u s j e donor_
    · exact old_raw_target_halo_at B pad coded portRoom haloRoom u s j e donor_

include measured ports signed coded positive in
theorem reached_selected_operand (v : B.next.V) (l : lane) (t : Fin (contactCount B))
    (sc : Bool) (a : (R).Contact) (rootAt : receiverRoot B (root v l)=center sc a)
    (key : donor_query B t=(sc,(Z).senderJoint T sc a)) (live : 0<(blocks B).count (contactParent B a))
    (fieldRoom : seat≤2^field) (tagRoom : (A).degree*seat<2^width)
    (portRoom : (A).degree+1<2^query) (haloRoom : (A).degree+2<2^cargo) (keys : DescentResetLocalRoster.rootSlots r (2^(Z).n)*(2^(Z).n+2^height)<2^field)
    (packed : seat*rad≤2^«meta») (which : Option Bool) :
    ((cells t).indicators.selected which (rank v) l).val=
      (match which with
       | none=>jointNumber B (root v l) (receiverRoot B (root v l)).1 (relativeShape B (root v l))
       | some e=>if relativeShape B (atSide sc a)=relativeShape B (root v l) then
           jointNumber B (root v l) (center e a).1 (relativeShape B (atSide e a)) else 0) := by
  obtain ⟨o,m,shapeAt,h⟩:=reached_raw_contact B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch «meta» v l t fieldRoom tagRoom portRoom haloRoom
  have side:=congrArg Prod.fst key
  rw [side] at o m h
  have room : (Z).senderJoint T sc a<2^field:=by
    have address : (donor_query B t).2 = (Z).senderJoint T sc a := congrArg Prod.snd key
    have cap : (donor_query B t).2≤DescentResetLocalRoster.rootSlots r (2^(Z).n)*(2^(Z).n+2^height):=
      (finProdFinEquiv.symm t).2.isLt
    rw [←address]
    exact cap.trans_lt keys
  exact selected_contact_joint B H M field query cargo groups (2^k) batch width «meta» (root v l) (rank v) l t
    (cells t) sc a rootAt key live o m shapeAt h room packed which

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

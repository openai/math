import OAI.Hierarchy.DescentContactOutputMeasured
import OAI.Hierarchy.DescentResetOriginalDonorMemory

namespace OAI
/-! Values issued by the original signed donor panels for every measured physical socket. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentSharedCableNames DescentIssuedFallbackPanel DescentPlainTerminal
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOldContactSender DescentGroupPeerOrder
open DescentContacts DescentDenseHostOrder DescentResetAttachments DescentStageEdgeReceipt DescentHostDirectory
open DescentPacking.PackedMatch.Local.Stage DescentContactDonorFront DescentContactPreROM DescentOldSenderReturn DescentResetOppositePayload
open DescentResetSignedHaloMatrix DescentPackedChildNeighbor.SIMD DescentContactProbePitch DescentContactCoordinateJoint
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

variable (newGroups newBlocks newBatch «meta» : ℕ)
local notation "out" => contactOutputs B H M field query cargo newGroups newBlocks newBatch width «meta»
local notation "sensor" => (out).rawIndicators base (Z).graph xs next raw
local notation:max "edge" c:arg => contactParent B c
local notation:max "site" s:arg c:arg => (if s then (blocks B).dst (edge c) else (blocks B).src (edge c))
local notation:max "center" s:arg c:arg => ((Z).rootVertex T ((R).owner s c),(Z).rootBlock T ((R).owner s c))
variable (queryWidth : (A).degree+1<2^query) (haloWidth : (A).degree+2<2^cargo)
  (shapeRoom : seat≤2^field) (markRoom : (A).degree*seat<2^width)
  (keys : DescentResetLocalRoster.rootSlots r (2^(Z).n)*(2^(Z).n+2^height)<2^field)
  (bounds : seat*2^(Nat.clog 2 ((A).degree+2))≤2^«meta»)

def originalChoices := DescentResetLocalRoster.rootSlots r (2^(Z).n)*(2^(Z).n+2^height)

theorem original_joint_room (s : Bool) (c : (R).Contact) : (Z).senderJoint T s c≤originalChoices B :=by
  let key:=DescentResetLocalRoster.rootId r (2^(Z).n) ((Z).rootTicket T ((R).owner s c))
  let socket : Fin (2^(Z).n+2^height):=⟨_,(Z).contactSlotWord_lt T s c⟩
  apply Nat.succ_le_of_lt
  change key.val * (2^(Z).n + 2^height) + socket.val < originalChoices B
  have bound := (finProdFinEquiv (key, socket)).isLt
  change socket.val + (2^(Z).n + 2^height) * key.val < originalChoices B at bound
  simpa only [Nat.add_comm, Nat.mul_comm] using bound

include measured ports signed coded positive queryWidth haloWidth in
/-- An occupied donor's two labels originate on the actual left and right incidences.
Vacant labels remain zero. The root halo uses its original one-based rank. -/
theorem original_numeric_fields (a short : ℕ) (labelRoom : originalChoices B<2^a)
    (shortRoom : max (originalChoices B) ((A).degree+2)<2^short)
    (innerRoom : (A).degree+2<2^«meta») (v : B.next.V) (l : lane) :
    let u:=root v l
    let t : Fin (contactCount B):=⟨0,by unfold contactCount DescentResetLocalRoster.rootSlots;positivity⟩
    let label:=local5 (rank v) l
    let rawHalo:=fun j=>(sensor t).halo false j (rank v) l
    (∀s j,(DescentContactWidthPage.recode a (label s j 0)).val=
      (originalDonor B u s j).elim 0 (fun e=>(Z).senderJoint T s ((R).contact e))) ∧
    (∀s j e,originalDonor B u s j=some e→
      (DescentContactWidthPage.recode short (label s j (if s then 1 else 0))).val=(Z).senderJoint T false ((R).contact e)) ∧
    ∀s j e,originalDonor B u s j=some e→
      (DescentContactWidthPage.recode short (DescentContactWidthPage.recode «meta» (rawHalo j))).val=
        haloNumber B u ((Z).rootVertex T ((R).owner false ((R).contact e)))+1 :=by
  intro u t label rawHalo
  let reached:=reached_donor_sensors B H M field query cargo base width pad xs next raw setup measured ports signed coded positive v l
  have lim (s : Bool) (c : (R).Contact) := original_joint_room B s c
  constructor
  · intro s j
    have labelEq:=reached.own s j
    have fit : (label s j 0).val<2^a:=by
      rw [show (label s j 0).val=_ from labelEq]
      cases hit : originalDonor B u s j with
      | none=>exact Nat.two_pow_pos _
      | some e=>exact (lim s _).trans_lt labelRoom
    exact (DescentContactWidthPage.recode_val _ fit).trans labelEq
  constructor
  · intro s j e hit
    have eqn : (label s j (if s then 1 else 0)).val=(Z).senderJoint T false ((R).contact e):=by
      cases s with
      | false =>
        change (label false j 0).val=_
        have own : (label false j 0).val = (originalDonor B u false j).elim 0
            (fun e => (Z).senderJoint T false ((R).contact e)) := reached.own false j
        rw [hit] at own
        exact own
      | true=>exact (reached.live true j e hit).1
    have fit : (label s j (if s then 1 else 0)).val<2^short := by
      rw [eqn];exact (lim false _).trans_lt ((le_max_left ..).trans_lt shortRoom)
    exact (DescentContactWidthPage.recode_val _ fit).trans eqn
  · intro s j e hit
    have previous:=actual_halo B H M field query cargo base width pad xs next raw ports signed coded newGroups newBlocks newBatch «meta»
      queryWidth haloWidth v l t s j e hit false
    have amount : (rawHalo j).val≤(A).degree+2:=by
      rw [show (rawHalo j).val=_ from previous]
      exact Nat.add_le_add_right (haloNumber_room B u _) 1
    have inner:=DescentContactWidthPage.recode_val (rawHalo j) (amount.trans_lt innerRoom)
    have outer:=DescentContactWidthPage.recode_val (DescentContactWidthPage.recode «meta» (rawHalo j))
      (inner.trans_lt (amount.trans_lt ((le_max_right ..).trans_lt shortRoom)))
    exact outer.trans (inner.trans previous)

local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth

/-- Physical donor-published blocks are in the original mixed-radix order of the
next group and within-group block. -/
theorem original_lane (g₁ : Fin (S.groupCount (i+1))) (x : Fin (2^k)) :
    ((digits).symm (g₁,x)).val=(finProdFinEquiv (g₁,x)).val:=rfl

theorem original_receiver (v : B.next.V) (g₁ : Fin (S.groupCount (i+1))) (x : Fin (2^k)) :
    contactReceiver B v ((digits).symm (g₁,x))=((g₁,v),x) :=by
  simp only [contactReceiver,Equiv.apply_symm_apply]

theorem original_lane_cast (eqn : 2^(T).commonDepth=S.groupCount (i+1)*2^k)
    (g₁ : Fin (S.groupCount (i+1))) (x : Fin (2^k)) :
    (finProdFinEquiv (g₁,x)).cast eqn.symm=(digits).symm (g₁,x):=Fin.ext rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

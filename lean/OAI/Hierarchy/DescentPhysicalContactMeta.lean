import OAI.Hierarchy.DescentContactCandidateRanks
import OAI.Hierarchy.DescentPhysicalMixedCapture

namespace OAI
/-! # The direct contact mask and its three native ranks in the same actor capture -/
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

variable {bw : ℕ} (first : ℕ) (U : DescentContactSenderDate.Prior (A).degree L (A).cap (Z).n r)
    (room : (X).Space base U bw) (past : (C₀).endAddress≤first) (area : (Y).endAddress first<2^bw)
local notation "oldCode" => (X).result base seat width U (Z).graph room
variable (packed : M*max (field*8) width≤bw/2) (early postTrunk : Memory bw)
    (received : (S₀).Before U xs next raw early)
    (oldEnd : (C₀).endAddress<2^bw)
    (stable : ∀a,a<(C₀).endAddress→postTrunk a=oldCode oldEnd packed early a)
    (jobs : (S₀).Packed bw) (views : M*max (field*(C₀).oldFields) (C₀).viewBits≤bw/2)
    (tailRoom : (Y).marker first+H*chunks J M<2^bw)
    (keys : DescentResetLocalRoster.rootSlots r (2^(Z).n)*(2^(Z).n+2^height)<2^field)
    (counter : M*max (field*(L*K+1)) field≤bw/2) (halo : (A).degree+2<2^cargo)
    (coord : seat*rad≤2^«meta») (newBatch : 0<batch)
local notation "dst" => (Y).issuedImage base first U postTrunk
local notation:max "port" x:arg t:arg f:arg => (Y).fieldExpr first x t f

local notation:max "site_" v:arg groupIx:arg x:arg => (((groupIx,v),x) : Host)
local notation:max "read_" t:arg f₀:arg v:arg groupIx:arg x:arg => operandDigit («meta»:=«meta») newBatch (port x t f₀) dst (rank v) groupIx

open DescentResetLocalRoster DescentParallelBase
open DescentDatedAddressBook
local notation "used" => Fintype.card B.next.V
local notation "names₀" => compactActorName B pad
local notation "dense₀" => compactActorOrder B pad
local notation "size₀" => H*seat
variable {date : PhysicalReset} {floor : ℕ} {I : date.DateInputs floor bw} {N₁ H₁ : ℕ} (lives : used≤H₁)
    (board : I.CandidateChannels) (name : Fin N₁→Fin I.masked.sparseHosts) (rankBase : ℕ)
    (banks : DescentResetPeerJointRAM.Sources) (priorMem : Memory bw)
local notation "co₀" => date.successor.contactShape
variable (rows₀ : Fin size₀→Fin 4→Option (Fin size₀))
    (fits₀ : DescentResetPeerJointRAM.Room banks rankBase H₁ size₀ H (A).degree bw)
    (stored₀ : DescentResetPeerJointRAM.Reads banks used names₀ (indexed rows₀) adj priorMem)
    (jointRoom : seat*DescentResetPeerJointRAM.radix (A).degree≤2^bw) (slotsRoom : 4≤2^I.masked.field)

/-- Assemble the four contact values and self marker while preserving the three captured ranks. -/
theorem contactMaskFields {α : Type} (a : Fin 9 → α) (values : Fin 4 → α) (own : α)
    (v0 : a 0 = values 0) (v1 : a 1 = values 1) (v2 : a 2 = values 2)
    (v3 : a 3 = values 3) (v7 : a 7 = own) (v8 : a 8 = values 0) :
    a = ![values 0, values 1, values 2, values 3, a 4, a 5, a 6, own, values 0] := by
  funext j
  fin_cases j
  · exact v0
  · exact v1
  · exact v2
  · exact v3
  · rfl
  · rfl
  · rfl
  · exact v7
  · exact v8

include measured ports signed coded positive past area received stable jobs views tailRoom keys counter halo coord newBatch
  fits₀ stored₀ jointRoom slotsRoom in
set_option maxHeartbeats 800000 in
theorem contact_present_word (word : «meta»*batch≤bw) (oldWord : L*K<2^field) (newWord : L*K<2^«meta»)
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
  let reached:=issuedContactMask B H M field query cargo base width pad batch I.masked.field first U postTrunk
    newBatch t v groupIx x ranks own
  let saved (j : Fin 4) : Cell I.masked.field := (operandDigit («meta»:=I.masked.field) newBatch ((contactOutputs B H M field query cargo groups (2^k) batch width I.masked.field).fieldExpr first x t j) ((contactOutputs B H M field query cargo groups (2^k) batch width I.masked.field).issuedImage base first U postTrunk) (rank v) groupIx : Cell I.masked.field)
  have source (j : Fin 4) :
      DescentResetDenseOperand.dense (H:=I.masked.hosts) name (board.contact x₀ t₀ j) h₀ g₀ =
        saved j:=by
    have operandRead:=reached_operand_digit B H M field query cargo base width pad xs next raw batch I.masked.field
      first U room past area packed early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord
      newBatch word t j v groupIx x
    have num:=(capture j).trans operandRead.symm
    exact Fin.ext (num.trans (Fin.val_cast_of_lt (num.symm.trans_lt (Fin.isLt _))).symm)
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
  apply reached_contact_meta B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch I.masked.field first U room past area packed early postTrunk received oldEnd stable jobs views tailRoom keys
    counter halo coord newBatch word oldWord newWord fieldRoom tagRoom portRoom v groupIx x t ranks own _ absent
  exact contact_mask_ranks B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch I.masked.field first U room past area packed early postTrunk received oldEnd stable jobs views tailRoom keys
    counter halo coord newBatch lives board name rankBase banks priorMem rows₀ fits₀ stored₀ jointRoom slotsRoom
    word oldWord newWord fieldRoom tagRoom portRoom v groupIx x t job x₀ t₀ h₀ g₀ sector capture peers menu

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

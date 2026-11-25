import OAI.Hierarchy.DescentContactRankRequests
import OAI.Hierarchy.DescentContactMaskRanks

namespace OAI
/-! True source, destination, and receiver ranks of the four observed original contact operands. -/
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

include measured ports signed coded positive past area received stable jobs views tailRoom keys counter halo coord newBatch
  fits₀ stored₀ jointRoom slotsRoom in
theorem contact_mask_ranks (word : «meta»*batch≤bw) (oldWord : L*K<2^field) (newWord : L*K<2^«meta»)
    (fieldRoom : seat≤2^field) (tagRoom : (A).degree*seat<2^width) (portRoom : (A).degree+1<2^query)
    (v : B.next.V) (groupIx : Fin groups) (x : Block k) (t : Fin (contactCount B))
    (job : ℕ) (x₀ : Fin (co₀).blocks) (t₀ : Fin (co₀).sockets) (h₀ : Fin I.masked.hosts) (g₀ : Fin I.masked.groups)
    (sector : date.successor.jobAt job=some (.inl (x₀,t₀)))
    (capture : ∀f₀ : Fin 4,(DescentResetDenseOperand.dense (H:=I.masked.hosts) name (board.contact x₀ t₀ f₀) h₀ g₀).val=
      ((cells t).indicators.output f₀ (rank v) ((digits).symm (groupIx,x))).val)
    (peers : present rows₀ (rank v)=(insert v (B.next.placement.near v)).map rank)
    (menu : ∀j,(board.peer j h₀ g₀).val=DescentResetPeerJointRAM.value H seat (A).degree adj used names₀ (indexed rows₀)
      ((dense₀ v).castLE lives) j)
    (a : Local (blocks B) (site_ v groupIx x)) (found : localOrigin B (site_ v groupIx x) (contactShelfIndex B t)=some a) :
    let u:=site_ v groupIx x
    (board.maskValues name job h₀ g₀ 4).val=localClass B u ((blocks B).src a.val) ∧
    (board.maskValues name job h₀ g₀ 5).val=localClass B u ((blocks B).dst a.val) ∧
    (board.maskValues name job h₀ g₀ 6).val=localClass B u u:=by
  intro u
  obtain ⟨old₀,old₁,left,right,here⟩:=contact_rank_requests B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch «meta» first U room past area packed early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch
    word oldWord newWord fieldRoom tagRoom portRoom v groupIx x t a found
  have chip (t₂ : Fin 4) :=(capture t₂).trans (reached_operand_digit B H M field query cargo base width pad xs next raw batch «meta»
    first U room past area packed early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch word t t₂ v groupIx x).symm
  have endpointAt (role : Fin 3) : board.endpoint name job role h₀ g₀ =
      DescentResetDenseOperand.dense (H:=I.masked.hosts) name (board.contact x₀ t₀ ⟨role.val+1,by omega⟩) h₀ g₀ := by
    unfold PhysicalReset.DateInputs.CandidateChannels.endpoint
    rw [sector]
  apply mask_ranks_local B pad lives board name rankBase banks priorMem rows₀ fits₀ stored₀ jointRoom slotsRoom u h₀ g₀ peers menu job a old₀ old₁
  · exact (congrArg Fin.val (endpointAt 0)).trans ((chip 1).trans left)
  · exact (congrArg Fin.val (endpointAt 1)).trans ((chip 2).trans right)
  · exact (congrArg Fin.val (endpointAt 2)).trans ((chip 3).trans here)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

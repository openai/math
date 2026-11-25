import OAI.Hierarchy.DescentReachedContactOperands

namespace OAI
/-! Actual endpoint requests at the local positive direct-contact slot. -/
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
include measured ports signed coded positive past area received stable jobs views tailRoom keys counter halo coord newBatch in
theorem contact_rank_requests (word : «meta»*batch≤bw) (oldWord : L*K<2^field) (newWord : L*K<2^«meta»)
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
  have rows_:=reached_live_contact B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch «meta» first U room past area packed early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch
    word oldWord newWord fieldRoom tagRoom portRoom v groupIx x t a sc atRoot named alive.1
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

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

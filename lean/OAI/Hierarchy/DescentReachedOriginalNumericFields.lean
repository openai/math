import OAI.Hierarchy.DescentResetOriginalDonorMeasured
import OAI.Hierarchy.DescentOriginalDonorDenseRead
import OAI.Hierarchy.DescentDensePhysicalOrder
import OAI.Hierarchy.DescentResetSignedAll

namespace OAI
/-! # Actual numbered donor words at the occupied dense recipient -/
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

local notation "groups" => S.groupCount (i+1)
local notation "blocks₀" => 2^k
local notation "O" => contactOutputs B H M field query cargo groups blocks₀ newBatch width «meta»
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "dir" => (Z).denseHostRank T (B.frame.host.symm.toEmbedding.trans host)
local notation "U" => Fintype.card B.next.V
variable (sel short : ℕ) (eqn : J=groups*blocks₀)
local notation "num" => (O).numberingLayout sel short
local notation "vv" => (O).numberingValues base (Z).graph xs next raw sel short eqn
variable (ls : originalChoices B<2^sel) (ss : max (originalChoices B) ((A).degree+2)<2^short)
  (inner : (A).degree+2<2^«meta»)

include measured ports signed coded positive queryWidth haloWidth ls ss inner in
theorem numbered_original_fields (v : B.next.V) (g₁ : Fin groups) (x : Fin blocks₀) :
    let u:=((g₁,v),x)
    let lane₁:=finProdFinEquiv (g₁,x)
    (∀s j,(DescentContactWidthPage.recode sel ((vv).label s j (rank v) lane₁)).val=
      (originalDonor B u s j).elim 0 (fun e=>(Z).senderJoint T s ((R).contact e))) ∧
    (∀s j e,originalDonor B u s j=some e→
      (DescentContactWidthPage.recode short ((vv).ticket s j (rank v) lane₁)).val=(Z).senderJoint T false ((R).contact e)) ∧
    ∀s j e,originalDonor B u s j=some e→
      (DescentContactWidthPage.recode short ((vv).halo j (rank v) lane₁)).val=
        haloNumber B u ((Z).rootVertex T ((R).owner false ((R).contact e)))+1:=by
  let high:=(finProdFinEquiv (g₁,x)).cast eqn.symm
  have atHost : contactReceiver B v high = ((g₁,v),x) :=
    (congrArg (contactReceiver B v) (original_lane_cast B eqn g₁ x)).trans (original_receiver B v g₁ x)
  have source:=original_numeric_fields B H M field query cargo base width pad xs next raw setup measured ports signed coded
    positive groups blocks₀ newBatch «meta» queryWidth haloWidth sel short ls ss inner v high
  dsimp only at source
  rw [atHost] at source
  exact source

/-- The true sparse physical rank of the actor at an occupied new ordinal. -/
def originalCompactName (ordinal : Fin U) : Fin (H*seat):=
  rank ((DescentStageEdgeReceipt.dense dir).symm ordinal)

theorem originalCompactName_read (v : B.next.V) : originalCompactName B H pad (dir v)=rank v:=by
  change rank ((DescentStageEdgeReceipt.dense dir).symm (DescentStageEdgeReceipt.dense dir v))=rank v
  exact congrArg (fun act : B.next.V => rank act) ((DescentStageEdgeReceipt.dense dir).symm_apply_apply v)

local notation "actual" => originalCompactName B H pad

include measured ports signed coded positive queryWidth haloWidth ls ss inner in
theorem occupied_numbered_fields {slots : ℕ} (used : U≤ slots) (u₀ : Fin slots) (v : B.next.V)
    (occupied : rackOf B ((dir).trans (Fin.castLEEmb used)) u₀=some v)
    (g₁ : Fin groups) (x : Fin blocks₀) :
    let u:=((g₁,v),x)
    (∀s j,((num).denseLabel actual vv x s j u₀ g₁).val=
      (originalDonor B u s j).elim 0 (fun e=>(Z).senderJoint T s ((R).contact e))) ∧
    (∀s j e,originalDonor B u s j=some e→
      ((num).denseCargo actual vv x s 0 j u₀ g₁).val=(Z).senderJoint T false ((R).contact e)) ∧
    ∀s j e,originalDonor B u s j=some e→
      ((num).denseCargo actual vv x s 1 j u₀ g₁).val=
        haloNumber B u ((Z).rootVertex T ((R).owner false ((R).contact e)))+1:=by
  have name:=(rack_named B _ u₀ v occupied).symm
  have ord : u₀.val=(dir v).val:=congrArg Fin.val name
  have below : u₀.val<U:=ord.trans_lt (dir v).isLt
  have atOrdinal : (⟨u₀.val,below⟩:Fin U)=dir v:=Fin.ext ord
  have source:=numbered_original_fields B H M field query cargo base width pad xs next raw setup measured ports signed coded
    positive newBatch «meta» queryWidth haloWidth sel short eqn ls ss inner v g₁ x
  simp only [DescentResetOriginalDonors.Layout.denseLabel,DescentResetOriginalDonors.Layout.denseCargo,
    DescentResetDenseOperand.dense,eq_self,ite_true,ite_eq_right (by decide : (1:Fin 2)≠0),dite_eq_left below,atOrdinal,
    originalCompactName_read]
  exact source

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

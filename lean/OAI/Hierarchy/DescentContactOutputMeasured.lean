import OAI.Hierarchy.DescentContactSelectedJoint
import OAI.Hierarchy.DescentContactHaloLimits
import OAI.Hierarchy.DescentContactMeasuredUnits

namespace OAI
/-! # Every original contact sensor used by the four-field native output -/
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

include signed ports coded queryWidth haloWidth in
theorem actual_halo (v : B.next.V) (l : lane) (t : Fin (contactCount B)) (s : Bool) (j : Fin (L*K))
    (e : (E).graph.Edge) (hit : originalDonor B (root v l) s j=some e) (other : Bool) :
    (((sensor t).halo other j (rank v) l).val)=haloNumber B (root v l) (center other ((R).contact e)).1+1:=by
  let u:=root v l
  let ptr:=host (oldV u)
  let pair:=finProdFinEquiv.symm j
  obtain ⟨hostEq,laneEq⟩:=actor_field B H pad v l
  have rowEq : ∀j,next ptr j=adj ptr j:=fun j=>(ports _ j).trans (host_at (A) host _ j).symm
  have same : short (b:=cargo) next id ptr=short (b:=cargo) adj id ptr:=by
    funext j
    exact congrArg (fun a : ℕ=>(a:Cell cargo)) (same_row next adj ptr rowEq j)
  have chip : raw pair.1 pair.2 ptr l=previousSigned (b:=field) (A) native S input.valid gr host words basis small pair.1 pair.2 ptr (oldG u):=by
    have cellAt := (signed (oldV u) l pair.1 pair.2).trans
      (previous_signed_at (b:=field) (A) native S input.valid gr host words basis small (oldV u) l pair.1 pair.2).symm
    exact cellAt.trans (congrArg (fun high => previousSigned (b:=field) (A) native S input.valid gr host words basis small pair.1 pair.2 ptr high) laneEq.symm)
  change (DescentPackedChildNeighbor.SIMD.lookup (short (b:=cargo) next id (DescentContactProbePitch.owner (rank v))) (if other then Right.askedField (A).degree (A).cap field query
    (raw pair.1 pair.2 (DescentContactProbePitch.owner (rank v)) l) 0 else askedField (A).degree (A).cap field query
    (raw pair.1 pair.2 (DescentContactProbePitch.owner (rank v)) l) 0) _).val=_
  rw [hostEq,same,chip]
  cases other
  · exact old_raw_halo_at B pad coded queryWidth haloWidth u s j e hit
  · exact old_raw_target_halo_at B pad coded queryWidth haloWidth u s j e hit

include measured ports signed coded positive shapeRoom markRoom queryWidth haloWidth keys bounds in
/-- The stated values are obtained from the exact five arrays in the executable
output period. A positive native tally supplies the original contact and signed grain. -/
theorem measured_joints (v : B.next.V) (l : lane) (t : Fin (contactCount B))
    (paid : 0<((sensor t).mass (rank v) l).val) :
    ∃c : (R).Contact,
      receiverRoot B (root v l)=center (donor_query B t).1 c ∧ (donor_query B t).2=(Z).senderJoint T (donor_query B t).1 c ∧
      0<(blocks B).count (contactParent B c) ∧
      ∀which,((sensor t).indicators.selected which (rank v) l).val=
        match which with
        | none=>jointNumber B (root v l) (receiverRoot B (root v l)).1 (relativeShape B (root v l))
        | some e=>if relativeShape B (site (donor_query B t).1 c)=relativeShape B (root v l) then
            jointNumber B (root v l) (center e c).1 (relativeShape B (site e c)) else 0:=by
  let u:=root v l
  let s:=(donor_query B t).1
  obtain ⟨hostEq,laneEq⟩:=actor_field B H pad v l
  have oldMass : ((sensor t).mass (rank v) l).val=
      (DescentContactSenderMass.Date.values S₀ (fun side j=>(S₀).sentValue xs side (phys j) 0) t (host (oldV u)) (oldG u)).val:=by
    exact congrArg₂ (fun h high => (DescentContactMaskShape.realAmount (X) base xs t h high).val) hostEq laneEq.symm
  obtain ⟨c,atRoot,named,present⟩:=positive_contact_mass B H M field query cargo base pad setup xs measured u t (oldMass ▸ paid)
  let current := reached_donor_sensors B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
  have direction : (out).socketWing t=donor_query B t:=rfl
  have shapeAt : ((sensor t).shape (rank v) l).val=relativeShape B u:=by
    apply (DescentContactProbePitch.shape_val (H:=H) (S:=seat) (G:=2^(T).commonDepth) shapeRoom (rank v) l).trans
    change (finProdFinEquiv.symm (finProdFinEquiv ((Z).hostFields T _ v))).2.val=_
    rw [Equiv.symm_apply_apply];rfl
  have exactLabel (j : Fin (L*K)) : ((sensor t).own j (rank v) l).val=
      (originalDonor B u s j).elim 0 (fun e=>(Z).senderJoint T s ((R).contact e)):= (current v l).own s j
  have exactMarker (j : Fin (L*K)) : ((sensor t).marker j (rank v) l).val=
      contactSheet B u t (finProdFinEquiv (finTwoEquiv.symm s,j)):=by
    let p:=finProdFinEquiv (finTwoEquiv.symm s,j)
    have measured_:=issued_contact_mark B ((X).endAddress base) H M field width pad local5 pair2 current shapeRoom markRoom t p v l
    have socket : (finProdFinEquiv.symm ((C₀).index t p)).1 = t :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (t,p))
    exact (congrArg (fun key => ((C₀).marker (Z).graph key
      ((C₀).values ys src ((C₀).index t p) (rank v) l)).val) socket).trans measured_
  have short : (Z).senderJoint T s c<2^field:=by
    rw [←named]
    exact lt_of_le_of_lt (finProdFinEquiv.symm t).2.isLt keys
  refine ⟨c,atRoot,named,present,fun which=>?_⟩
  exact selected_contact_joint B H M field query cargo newGroups newBlocks newBatch width «meta» u (rank v) l t (sensor t) s c atRoot
    (Prod.ext rfl named) present exactLabel exactMarker shapeAt
    (fun j e got end_=>actual_halo B H M field query cargo base width pad xs next raw ports signed coded newGroups newBlocks newBatch «meta»
      queryWidth haloWidth v l t s j e got end_) short bounds which

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

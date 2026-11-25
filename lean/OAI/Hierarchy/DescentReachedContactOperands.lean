import OAI.Hierarchy.DescentContactReachedIndicators
import OAI.Hierarchy.DescentContactHaloRoom

namespace OAI
/-! # Executed four-field contact outputs on the reached reset and its genuine output groups -/
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

include past area received stable jobs views tailRoom keys counter halo coord newBatch in
/-- Unconditional on the existence of a contact. This is the packed read for the entire
previous-host-by-shape raster, including missing owners and unoccupied directional slots.
The new group and low block use the actual calendar digits. -/
theorem reached_contact_operands (t : Fin (contactCount B)) (f₀ : Fin 4) (x : Block k) :
    (port x t f₀).Fits bw ((Y).endAddress first) ∧ Source (port x t f₀)
      (fun h groupIx=>(cells t).indicators.output f₀ h ((digits).symm (groupIx,x))) batch dst := by
  have result:=(Y).attained_fields base first U (Z).graph room past area packed xs next raw early postTrunk received stable
    jobs views tailRoom keys counter halo coord newBatch (Nat.two_pow_pos k) jobs.positive (contact_group_digits B) t f₀ x
  change (port x t f₀).Fits bw ((Y).endAddress first) ∧ Source (port x t f₀)
      (fun h (groupIx : Fin groups) => (cells t).indicators.output f₀ h
        (Fin.cast (contact_group_digits B).symm (finProdFinEquiv (groupIx,x)))) batch dst at result
  have laneMap : (fun (h : Fin (H*seat)) (groupIx : Fin groups) =>
      (cells t).indicators.output f₀ h (Fin.cast (contact_group_digits B).symm (finProdFinEquiv (groupIx,x)))) =
      (fun h groupIx => (cells t).indicators.output f₀ h ((digits).symm (groupIx,x))) := by
    funext h groupIx
    exact congrArg ((cells t).indicators.output f₀ h) (original_contact_lane B groupIx x)
  exact ⟨result.1, Eq.mp (congrArg (fun values => Source (port x t f₀) values batch dst) laneMap) result.2⟩

/-- The exact packed result address uses the new host, the quotient of its group by the
new batch, and the remainder within that word. -/
def fieldChunk {«groups» batch : ℕ} (hb : 0<batch) (groupIx : Fin «groups») : Fin (chunks «groups» batch) :=
  ⟨groupIx.val/batch,(Nat.div_lt_iff_lt_mul hb).2 (groupIx.isLt.trans_le (by
    simpa [chunks,Nat.mul_comm] using ThreeFlat.Routing.CallPool.count_le_batches_mul «groups» batch hb))⟩

def operandDigit {bw H «groups» batch «meta» : ℕ} (hb : 0<batch) (op : Expr) (mem : Memory bw) (v : Fin H) (groupIx : Fin «groups») : ℕ :=
  digit «meta» (groupIx.val%batch) (op.eval mem ((row H «groups» batch (v,fieldChunk hb groupIx)).val:Word bw)).val

private theorem source_digit {bw H «groups» batch «meta» : ℕ} (hb : 0<batch) (size : «meta»*batch≤bw) (op : Expr)
    (mem : Memory bw) (value : Fin H→Fin «groups»→Cell «meta») (read : Source op value batch mem) (v : Fin H) (groupIx : Fin «groups») :
    operandDigit («meta»:=«meta») hb op mem v groupIx=(value v groupIx).val := by
  let part:=fieldChunk hb groupIx
  let j : Fin batch:=⟨groupIx.val%batch,Nat.mod_lt _ hb⟩
  have idx:part.val*batch+j.val=groupIx.val:=by simpa [part,fieldChunk,j,Nat.mul_comm] using Nat.div_add_mod groupIx.val batch
  have digitBound:part.val*batch+j.val<«groups»:=idx.trans_lt groupIx.isLt
  have includeWord:=(data (M:=batch) value (v,part)).isLt.trans_le (Nat.pow_le_pow_right (by decide) size)
  unfold operandDigit
  rw [read (v,part),Fin.val_cast_of_lt includeWord]
  change digit «meta» j.val ((encode «meta» batch _).val)=_
  rw [digit_encode,dite_eq_left digitBound]
  exact congrArg (fun groupIx=> (value v groupIx).val) (Fin.ext idx)

local notation:max "site_" v:arg groupIx:arg x:arg => (((groupIx,v),x) : Host)
local notation:max "read_" t:arg f₀:arg v:arg groupIx:arg x:arg => operandDigit («meta»:=«meta») newBatch (port x t f₀) dst (rank v) groupIx

include past area received stable jobs views tailRoom keys counter halo coord newBatch in
/-- For every measured receiver, including an empty socket, read the actual physical digit
of its packed output without a hypothetical per-site Expr or an auxiliary second scan. -/
theorem reached_operand_digit (word : «meta»*batch≤bw) (t : Fin (contactCount B)) (f₀ : Fin 4) (v : B.next.V)
    (groupIx : Fin groups) (x : Block k) :
    read_ t f₀ v groupIx x=((cells t).indicators.output f₀ (rank v) ((digits).symm (groupIx,x))).val := by
  have load:=(reached_contact_operands B H M field query cargo base width xs next raw batch «meta» first U room past area packed
    early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch t f₀ x).2
  exact source_digit newBatch word _ _ _ load (rank v) groupIx

include measured ports signed coded positive past area received stable jobs views tailRoom keys counter halo coord newBatch in
theorem reached_live_contact (word : «meta»*batch≤bw) (oldWord : L*K<2^field) (newWord : L*K<2^«meta»)
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
  have op:=reached_operand_digit B H M field query cargo base width pad xs next raw batch «meta» first U room past area packed
    early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch word t f₀ v groupIx x
  rw [op]
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
  have quantity : (blocks B).count (contactParent B a)≤L*K:=by
    rw [←physicalValue]
    apply le_trans (Nat.mod_le _ _) (DescentContactSenderMass.bounded _ _)
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

include past area received stable jobs views tailRoom keys counter halo coord newBatch in
theorem reached_count_digit (word : «meta»*batch≤bw) (newWord : L*K<2^«meta»)
    (v : B.next.V) (groupIx : Fin groups) (x : Block k) (t : Fin (contactCount B)) :
    read_ t 0 v groupIx x=oldMass t (site_ v groupIx x) := by
  let u:=site_ v groupIx x
  let hi:=(digits).symm (groupIx,x)
  have same:=reached_contact_receiver B v groupIx x
  have geo:=actor_field B H pad v hi
  have receipt:=reached_operand_digit B H M field query cargo base width pad xs next raw batch «meta» first U room past area packed
    early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch word t 0 v groupIx x
  rw [receipt]
  change (DescentContactWidthPage.recode «meta» (DescentContactMaskShape.realAmount X base xs t
    (DescentContactProbePitch.owner (rank v)) hi)).val=_
  refine (congrArg₂ (fun a b=>(DescentContactWidthPage.recode «meta»
    (DescentContactMaskShape.realAmount X base xs t a b)).val) geo.1 geo.2.symm).trans ?_
  rw [same]
  have bounded : oldMass t u≤L*K:=(Nat.mod_le _ _).trans (DescentContactSenderMass.bounded _ _)
  exact Fin.val_cast_of_lt (bounded.trans_lt newWord)

/-- Inputs of the reached contact mask. Four fields read actual projected bits and the
first repeated field supplies the measured grain count. Ranks come from their three separate native columns. -/
def issuedContactMask (t : Fin (contactCount B)) (v : B.next.V) (groupIx : Fin groups) (x : Block k)
    (ranks : Fin 3→Cell «meta») (self : Cell «meta») : Fin 9→Cell «meta» :=
  let physical : Fin 4→Cell «meta»:=fun registerIx=>(read_ t registerIx v groupIx x : ℕ)
  ![physical 0,physical 1,physical 2,physical 3,ranks 0,ranks 1,ranks 2,self,physical 0]

include measured ports signed coded positive past area received stable jobs views tailRoom keys counter halo coord newBatch in
theorem reached_contact_meta (word : «meta»*batch≤bw) (oldWord : L*K<2^field) (newWord : L*K<2^«meta»)
    (fieldRoom : seat≤2^field) (tagRoom : (A).degree*seat<2^width) (portRoom : (A).degree+1<2^query)
    (v : B.next.V) (groupIx : Fin groups) (x : Block k) (t : Fin (contactCount B)) (ranks : Fin 3→Cell «meta») (self : Cell «meta»)
    (rankRead : ∀p,localOrigin B (site_ v groupIx x) (contactShelfIndex B t)=some p→
      (ranks 0).val=localClass B (site_ v groupIx x) ((blocks B).src p.val) ∧
      (ranks 1).val=localClass B (site_ v groupIx x) ((blocks B).dst p.val) ∧
      (ranks 2).val=localClass B (site_ v groupIx x) (site_ v groupIx x))
    (absent : self.val≠0 ↔ (site_ v groupIx x)∉Stage.near B.next.placement (site_ v groupIx x)) :
    let u:=site_ v groupIx x
    let actual:=issuedContactMask B H M field query cargo base width pad batch «meta» first U postTrunk newBatch t v groupIx x ranks self
    DescentCandidateMaskRAM.render actual=DescentResetFieldAssembler.raw «meta» (Hierarchy.DescentSixParty.ClosedReset.Window.meta B u (localOrigin B u (contactShelfIndex B t))) := by
  intro u actual
  let s:=(donor_query B t).1
  have physicalValue (registerIx : Fin 4) : ((read_ t registerIx v groupIx x : ℕ):Cell «meta»).val=read_ t registerIx v groupIx x:=by
    let fieldRead:=reached_operand_digit B H M field query cargo base width pad xs next raw batch «meta» first U room past area packed
      early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch word t registerIx v groupIx x
    exact Fin.val_cast_of_lt (fieldRead.trans_lt (Fin.isLt _))
  have countRead:=reached_count_digit B H M field query cargo base width pad xs next raw batch «meta» first U room past area packed
    early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch word newWord v groupIx x t
  have money : (actual 8).val=oldMass t u:=(physicalValue 0).trans countRead
  apply contact_program_meta B H M field query cargo base pad setup xs measured u t actual (fun z=>Nat.ne_of_gt (money.symm ▸ z))
    money _ oldWord rankRead absent
  intro a countAt roots key
  have matched : donor_query B t=(s,(Z).senderJoint T s a):=Prod.ext rfl key
  have enough:=paid_contact_mass B H M field query cargo base pad setup xs measured u t a roots key oldWord
  have live : 0<(blocks B).count (contactParent B a):=by rw [←enough];exact countAt
  have actualFields:=reached_live_contact B H M field query cargo base width pad xs next raw setup measured ports signed coded positive
    batch «meta» first U room past area packed early postTrunk received oldEnd stable jobs views tailRoom keys counter halo coord newBatch
    word oldWord newWord fieldRoom tagRoom portRoom v groupIx x t a s roots matched live
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

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

import OAI.Hierarchy.DescentInstalledPortKeys
import OAI.Hierarchy.DescentResetOriginalOperandSite
import OAI.Hierarchy.DescentClosedDeviceArgumentKeys
import OAI.Hierarchy.DescentCalendarPublicSocketField
import OAI.Hierarchy.DescentRotorApertureLane

namespace OAI
/-! # Word and endpoint of the installed public rotor contact -/
namespace Hierarchy.DescentResetLaneIssue
open DescentLaneGates DescentBatchedRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open DescentRotor DescentRouterSlots Computability.BorderVNP.Crossing
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun x : Item contact owner s w => first (root contact input site owner s w align x))
    (fun x : Item contact owner s w => last (link contact owner s w x)) pay) (key : I↪Fin num)
local notation "sourceSite" => (fun x : Item contact owner s w => first (root contact input site owner s w align x))
local notation "targetSite" => (fun x : Item contact owner s w => last (link contact owner s w x))
local notation "Index" => Item contact owner s w
local notation "device" => DescentGoodRouter.device D (m*p) contact input site owner align s w G first last P
local notation "host" => Physical.host G.arcs D P.layers C₀ b (m*p)
local notation "socketKey" => DescentOrderedReset.itemKey key contact owner s w

open DescentOrderedReset
open DescentRotorOperandQueryROM.Shape
local notation "ord" => Ordered.orderedAddress socketKey sourceSite targetSite hw
local notation "selected" => fun (side : Bool) (v : Fin (2^n)) (r : Fin P.layers) (j : Fin b) (e : Index) => ((if side then targetSite e else sourceSite e)=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j)
local notation "get" => publicTapLane D (m*p) contact input site owner align s w G first last P key
  (m:=m) (p:=p) rfl hp

private abbrev contactSourceWidth {Port : Type} {packet : ℕ} {width : Port → ℕ} (_ : LaneSource packet width) := width

omit [Fintype R] in
/-- On the occupied target leg the port is the public contact socket of
the very same grain used by the aperture's order statistic. -/
theorem public_contact_lane (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m)
    (j : Fin b) (e : Index) (arrived : selected true v r j e) :
    ∃ (l : Lane p (contactSourceWidth (get true v r k j)))
      (atSite : (device).attach (linkSlot D contact input site owner (fun _ : I=>(m*p)) s w (link contact owner s w e))=
        tap host (.inl (v,true))),
      get true v r k j=.wire l ∧ l.port=.inr ⟨linkSlot D contact input site owner (fun _ : I=>(m*p)) s w
        (link contact owner s w e),atSite⟩ :=by
  change targetSite e=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j at arrived
  obtain ⟨rfl,rfl,rfl⟩:=arrived
  let item : {i : Index // targetSite i=targetSite e}:=⟨e,rfl⟩
  let l:=trueLane D (m*p) contact input site owner align s w G first last P key (m:=m) (p:=p) rfl _ k item hp
  have issued : get true (targetSite e) (P.choose (ord e).1) k (ord e).2=.wire l :=by
    have focusEq : Ordered.focus ord (fun z=>(P.choose z,z.2.1)) targetSite (fun _=>rfl)
        (P.choose (ord e).1) (targetSite e) (ord e).2=.inr item :=
      realized_focus G P socketKey true e
    exact congrArg (focusLane (fun t => trueLane D (m*p) contact input site owner align s w G first last P key
      (m:=m) (p:=p) rfl (targetSite e) k t hp)) focusEq
  have siteAt : (device).attach (linkSlot D contact input site owner (fun _ : I=>(m*p)) s w (link contact owner s w e))=
      tap host (.inl (targetSite e,true)) :=by
    change tap host (.inl (DescentGoodRouter.position D (m*p) contact input site owner s w first last _))=_
    apply congrArg (fun q=>tap host (.inl q))
    simp [DescentGoodRouter.position]
  exact ⟨l,siteAt,issued,rfl⟩

end
end Hierarchy.DescentResetLaneIssue

namespace Hierarchy.DescentSixParty.ResetInput
open DescentBundleHistory DescentRetainedRangeDigits DescentBatchedBank
open Computability.BorderVNP.Crossing DescentRotor DescentChosenRouter DescentKernelHistory DescentResetGates
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin L)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
local notation "R" => Z.placement
local notation "chosen" => DescentChosenRouter.selected R Z.graph Z.positive Z.pay Z.circuit

local notation "rack" => DescentRouterBank.network d (R).contact (R).input (R).site (R).owner (fun _ : A.graph.Edge=>Z.unit)
local notation "devices" => fun u : (rack).Site=>DescentMixedRouter.device Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align (D:=d) (chosen u.1 u.2)
local notation "localProgram" => sizedLocal Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen
local notation "nodes" => sizedLocalNode Z.graph Z.positive Z.unit m p hp fit (R).contact (R).input (R).site (R).owner (R).align key d chosen


open private DescentNetworkSubstitution.sourceTap_at DescentNetworkSubstitution.targetTap_at from OAI.Hierarchy.DescentNetworkSubstitution

/-- Following an actual public contact through the bank substitution gives
the shared graph edge, with the correct orientation at both devices. -/
theorem bank_word_contact (side : Bool) (root : (R).Good) (e : DescentChosenRouter.Cells R side root)
    (v : (devices (side,.inl root)).Site)
    (r : BlockRef p (boundaryWidth (devices (side,.inl root)) v))
    (atSite : (devices (side,.inl root)).attach (DescentRouterSlots.linkSlot d (R).contact (R).input (R).site (R).owner
      (fun _ : A.graph.Edge=>Z.unit) side (.inl root) (DescentRouterSlots.link (R).contact (R).owner side (.inl root) e))=v)
    (localPort : r.port=.inr ⟨_,atSite⟩) :
    ∃edge,(Z.bankPorts ⟨(side,.inl root),v⟩).slot r.port=Sum.inl edge ∧
      edge.val=Sum.inl ((R).contact e.val) ∧
      (if side then Z.bank.dst edge.val else Z.bank.src edge.val)=⟨(side,.inl root),v⟩ ∧
      ((Z.bankPorts ⟨(side,.inl root),v⟩).wordBlock r).block=r.block :=by
  rw [localPort]
  cases side with
  | false=>
    refine ⟨_,rfl,rfl,?_,rfl⟩
    exact (DescentNetworkSubstitution.sourceTap_at rack devices ⟨(R).contact e.val,
      congrArg (Prod.mk false) e.property⟩).trans (congrArg (Sigma.mk _) atSite)
  | true=>
    refine ⟨_,rfl,rfl,?_,rfl⟩
    exact (DescentNetworkSubstitution.targetTap_at rack devices ⟨(R).contact e.val,
      congrArg (Prod.mk true) e.property⟩).trans (congrArg (Sigma.mk _) atSite)

end
end Hierarchy.DescentSixParty.ResetInput
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one wide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts installed
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "world" => B.reset.orderedOrdinary B.terminals birth
local notation "cnt" => fun e=>(coarse).graph.width e/B.reset.unit
local notation "geo" => B.reset.counts_fit B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "tape" => B.reset.nativeResetEdges B.terminals vertexCode birth
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw ((tape).order.trans Fin.valEmbedding) S B.valid rawSite
local notation "edgeName" => DescentPhysicalOrder.rename sparse



open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "raw_" => W.granular B.count (z*G.b) B.fit
local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
local notation "where_" x:arg => resetOrigin B hp whole a x
local notation "dev_" => B.reset.laneShape birth unit p hp splitEq
local notation "loc_" => fun e : (raw_).graph.Edge=>B.terminals.home ((raw_).graph.dst e)

open DescentLaneGates
local notation "prog_" v:arg => B.reset.laneProgram birth unit p hp splitEq v
local notation "words_" v:arg => fun t : Boundary B.reset.bank v=>boundaryWidth B.reset.bank v t/p
local notation "fit_" v:arg => B.reset.laneWidth_eq unit p splitEq v


set_option quotPrecheck false
local notation "rawEdge" => (W.granular B.count (z*G.b) B.fit).graph.Edge
local notation "contact_" e:arg => B.reset.placement.contact e

/-- The word on an installed public contact is the chosen old contact's
word in the reentered graph.  Its physical orientation may be either face. -/
theorem device_route_contact (v : B.reset.bank.Site)
    (r : BlockRef p (boundaryWidth B.reset.bank v))
    (edge : {a : B.reset.bank.Edge // B.reset.bank.src a=v ∨ B.reset.bank.dst a=v})
    (e : rawEdge) (portAt : r.port=.inl edge) (genuine : edge.val=.inl (contact_ e)) :
    deviceRoute B hp v r=(contactParent B (contact_ e),r.block) :=by
  rcases r with ⟨port,word,room⟩
  dsimp only at portAt
  subst port
  change ((motherNames B).symm (.inr (.inr edge.val)),word)=_
  rw [genuine]
  rfl

private theorem sameCard {T : Type} (i j : Fintype T) :
    @Fintype.card T i = @Fintype.card T j :=
  congrArg (@Fintype.card T) (Subsingleton.elim i j)

include hp pos in
/-- The actual aligned word fits the original contact fibre. -/
theorem contact_block_room (v : B.reset.bank.Site) (r : BlockRef p (boundaryWidth B.reset.bank v))
    (edge : {a : B.reset.bank.Edge // B.reset.bank.src a=v ∨ B.reset.bank.dst a=v}) (e : rawEdge)
    (portAt : r.port=.inl edge) (genuine : edge.val=.inl (contact_ e))
    (split : ℕ) (radix : B.reset.unit=split*p) :
    r.block/split<Fintype.card {j : rawEdge // contact_ j=contact_ e} :=by
  have bound:=r.fits
  rw [portAt] at bound
  change (r.block+1)*p≤B.reset.bank.width edge.val at bound
  rw [genuine] at bound
  change (r.block+1)*p≤DescentNamedContact.width B.reset.placement.contact
    (fun _ : rawEdge => B.reset.unit) (contact_ e) at bound
  simp only [DescentNamedContact.width,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at bound
  have scale (count : ℕ) : count * B.reset.unit = (count * split) * p :=
    (congrArg (count * ·) radix).trans (Nat.mul_assoc count split p).symm
  have short := Nat.le_of_mul_le_mul_right (bound.trans_eq (scale _)) hp
  have nonzero : 0<split := Nat.pos_of_ne_zero (fun h =>
    (Nat.ne_of_gt pos) (radix.trans (by rw [h,Nat.zero_mul])))
  apply (Nat.div_lt_iff_lt_mul nonzero).mpr
  exact (Nat.lt_of_succ_le short).trans_eq
    (congrArg (· * split) (sameCard _ _))

theorem contact_socket_face {field query lanes batches split nodes args grain : ℕ}
    (side : Bool) (root : B.reset.placement.Good) (e : DescentChosenRouter.Cells B.reset.placement side root)
    (word : ℕ) (owns : word/split<Fintype.card {j : rawEdge // contact_ j=contact_ e.val}) :
    (reached_contact_socket (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
      (split:=split) (nodes:=nodes) (args:=args) (grain:=grain) B side root e word owns).face.val=
      (contactParent B (contact_ e.val),side) :=by
  exact (Classical.choose_spec (original_word_contact (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (split:=split) (nodes:=nodes) (args:=args) (grain:=grain) B side root e)).1

/-- Undoing the archived gate's renaming returns the signed endpoint of
this exact contact.  The endpoint is read from the global bank substitution. -/
theorem device_contact_site (x : NodeOrder.All next_) (v : B.reset.bank.Site)
    (u : (prog_ v).Node) (origin : where_ x=.inr (.inr ⟨v,u⟩)) (side : Bool)
    (e : rawEdge) (edge : B.reset.bank.Edge) (genuine : edge=.inl (contact_ e))
    (atEnd : (if side then B.reset.bank.dst edge else B.reset.bank.src edge)=v) :
    (hop).symm x.1=if side then (coarse).graph.dst (contactParent B (contact_ e))
      else (coarse).graph.src (contactParent B (contact_ e)) :=by
  have here:=device_wire_original_site B hp whole a x v u origin edge side atEnd
  subst edge
  exact here

/-- The original returned socket and the actual post-installation node share
the same physical edge and old word. -/
theorem device_contact_key {field query lanes batches split nodes args grain : ℕ}
    (x : NodeOrder.All next_) (v : B.reset.bank.Site) (u : (prog_ v).Node)
    (origin : where_ x=.inr (.inr ⟨v,u⟩)) (slot : ℕ) (side : Bool)
    (root : B.reset.placement.Good) (e : DescentChosenRouter.Cells B.reset.placement side root)
    (r : BlockRef p (boundaryWidth B.reset.bank v))
    (edge : {a : B.reset.bank.Edge // B.reset.bank.src a=v ∨ B.reset.bank.dst a=v})
    (portAt : r.port=.inl edge) (genuine : edge.val=.inl (contact_ e.val)) (radix : B.reset.unit=split*p)
    (read : ((dev_ v).keys u)[slot]?=some (.inl r)) :
    let owns:=contact_block_room B hp pos v r edge e.val portAt genuine split radix
    let found:=reached_contact_socket (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
      (split:=split) (nodes:=nodes) (args:=args) (grain:=grain) B side root e r.block owns
    keyCable installed (middle_ x) slot=some (found.face.val.1,r.block) ∧ found.face.val.2=side :=by
  intro owns found
  have face:=contact_socket_face (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (split:=split) (nodes:=nodes) (args:=args) (grain:=grain) B side root e r.block owns
  exact ⟨(device_route_key B hp one pos whole wide a sh x v u origin slot r read).trans
    (congrArg some ((device_route_contact B hp v r edge e.val portAt genuine).trans
      (congrArg (fun s=>(s.1,r.block)) face.symm))),congrArg Prod.snd face⟩

/-- Positive public tap, in the same form as the incoming-stem socket.
All covered words use this contact even when their consecutive old donor changes. -/
theorem good_tap_contact_socket_key {field query lanes batches nodes args grain : ℕ}
    (y : NodeOrder.All next_) (v : B.reset.bank.Site) (u : (prog_ v).Node)
    (origin : where_ y=.inr (.inr ⟨v,u⟩)) (j : ℕ) (side : Bool)
    (root : B.reset.placement.Good) (e : DescentChosenRouter.Cells B.reset.placement side root)
    (r : BlockRef p (boundaryWidth B.reset.bank v)) (edge : Incident B.reset.bank v)
    (portAt : r.port=.inl edge) (genuine : edge.val=.inl (contact_ e.val))
    (atEnd : (if side then B.reset.bank.dst edge.val else B.reset.bank.src edge.val)=v)
    (read : ((dev_ v).keys u)[j]?=some (.inl r)) :
    let mother:=contactParent B (contact_ e.val)
    let home:=if side then (blocks B).dst mother else (blocks B).src mother
    let number:=(publicOperandConfig B field query lanes batches unit nodes args grain).rotorContactAt
      side cap.placement.cap (B.reset.goodLabel B.terminals root)
      (DescentChosenRouter.target B.reset.placement side root e)
    ∃out : PublicSocket B home unit r.block true number,
      keyCable installed (middle_ y) j=some (out.face.val.1,r.block) ∧
      (if out.face.val.2 then (coarse).graph.dst out.face.val.1 else (coarse).graph.src out.face.val.1)=(hop).symm y.1 :=by
  intro mother home number
  let owns:=contact_block_room B hp pos v r edge e.val portAt genuine unit splitEq
  let out:=reached_contact_socket (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (split:=unit) (nodes:=nodes) (args:=args) (grain:=grain) B side root e r.block owns
  have key:=device_contact_key (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (split:=unit) (nodes:=nodes) (args:=args) (grain:=grain)
    B hp one pos whole wide a sh y v u origin j side root e r edge portAt genuine splitEq read
  have recv:=device_contact_site B hp whole a y v u origin side e.val edge.val genuine atEnd
  have face:=contact_socket_face (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (split:=unit) (nodes:=nodes) (args:=args) (grain:=grain) B side root e r.block owns
  change out.face.val=(mother,side) at face
  refine ⟨out,key.1,?_⟩
  rw [face]
  exact recv.symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

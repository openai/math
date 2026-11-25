import OAI.Hierarchy.DescentMountedGoodKeys
import OAI.Hierarchy.DescentInstalledRotorContact

namespace OAI
/-! # The original installed tap and every word in its occupied contact lane -/
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
local notation "socketKey" => DescentOrderedReset.itemKey key contact owner s w

open DescentOrderedReset
open DescentRotorOperandQueryROM.Shape DescentResetPublicOperandBook
local notation "ord" => Ordered.orderedAddress socketKey sourceSite targetSite hw
local notation "selected" => fun (side : Bool) (v : Fin (2^n)) (r : Fin P.layers) (j : Fin b) (e : Index) => ((if side then targetSite e else sourceSite e)=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j)
local notation "get" => publicTapLane D (m*p) contact input site owner align s w G first last P key
  (m:=m) (p:=p) rfl hp

private abbrev mountedSourceWidth {Port : Type} {packet : ℕ} {width : Port → ℕ} (_ : LaneSource packet width) := width

omit [Fintype R] in
/-- Resolve the original operand's absolute word, including its second
covered word.  Every public rotor lane has stride one. -/
theorem public_focus_word (dir : Bool) (v : Fin (2^n)) (r : Fin P.layers) (k : Fin m)
    (j : Fin b) (within : ℕ) (e : Index) (arrived : selected dir v r j e)
    (l : Lane p (mountedSourceWidth (get dir v r k j))) (issued : get dir v r k j=.wire l) :
    let first:=Config.earlierCount sourceSite targetSite socketKey (⟨dir,v,r.val,k.val,j.val,within⟩ : Mouth n) e*m+k.val
    l.bundleStart=first ∧ l.count (fun z=>mountedSourceWidth (get dir v r k j) z/p)=
      min 2 (Fintype.card (DescentRotorOperandRanks.At sourceSite targetSite (fun z=>(if dir then z.2 else z.1)=v))*m-first) :=by
  intro startWord
  obtain ⟨l',eqn,start,stride,span⟩:=public_lane_at D m p hp contact input site owner align s w
    G first last P key dir v r k j within e arrived
  have same : l'=l:=LaneSource.wire.inj (eqn.symm.trans issued)
  subst l'
  have stored : l.bundleStart=startWord:=by
    change l.start/p=startWord
    rw [start,Nat.mul_div_cancel _ hp]
  exact ⟨stored,by simp [Lane.count,stored,stride,span]⟩
end
end Hierarchy.DescentResetLaneIssue
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentRouterSlots DescentBatchedBank DescentBundleHistory DescentRetainedRangeDigits DescentBatchedNodeOrder
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
    {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
    (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "sel" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align sel D
local notation "prg" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D sel
variable (s : Bool) (g : P.Good)
local notation "r" => (⟨s,.inl g⟩ : Bool×P.Site)
local notation "sizedHardware" => (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay)
local notation "sizedChoice" => selected P G hw pay sizedHardware s (.inl g)
local notation "trueDevice" => DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align
  (D:=D) sizedChoice
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay hardware s g) C₀ bits u
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "prog" v:arg => (DescentBatchedBank.deviceProgram G hw m p hp P.contact P.input P.site P.owner
  P.align key D sizedChoice (sizedSite v))
local notation "widthAt" v:arg => (boundaryWidth trueDevice (sizedSite v))
local notation:max "venue" v:arg => (⟨r,installedSite v⟩ : (bank).Site)
variable (v : (DescentCommonPalette.rotor G).Site)


open DescentLaneGates

local notation "itemEnum" => @Subtype.fintype I (fun a => P.owner s (P.contact a) = Sum.inl g)
  (fun _ => Classical.propDecidable _) inferInstance
local notation "base" => (transportCircuit (b:=itemEnum) (G:=G) (hw:=hw) (pay:=pay) (sizedHardware s g))

local notation "rack" => DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I=>u)
local notation "devices" => fun a : (rack).Site=>DescentMixedRouter.device G hw u P.contact P.input P.site P.owner P.align
  (D:=D) (sel a.1 a.2)


open DescentPhysicalSplit DescentLaneGates
set_option quotPrecheck false
open private DescentNetworkSubstitution.sourceTap_at DescentNetworkSubstitution.targetTap_at from OAI.Hierarchy.DescentNetworkSubstitution

/-- The cast to the chosen good device leaves the outer contact identifier
and its endpoint intact. -/
theorem mountedGood_contact (e : Cells P s g) (ref : BlockRef p (boundaryWidth trueDevice (sizedSite v)))
    (atSite : (trueDevice).attach (linkSlot D P.contact P.input P.site P.owner (fun _ : I=>m*p) s (.inl g)
      (link P.contact P.owner s (.inl g) e))=sizedSite v)
    (inner : ref.port=.inr ⟨_,atSite⟩) :
    ∃edge,((mountedGoodPorts P G hw pay hardware D m p fit s g v).wordBlock ref).port=.inl edge ∧
      edge.val=.inl (P.contact e.val) ∧ (if s then (bank).dst edge.val else (bank).src edge.val)=venue v ∧
      ((mountedGoodPorts P G hw pay hardware D m p fit s g v).wordBlock ref).block=ref.block :=by
  revert hardware ref atSite inner
  subst u
  intro mounted ref atSite inner
  let rack₀ := DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I => m*p)
  let devices₀ := fun a : rack₀.Site => DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align
    (D:=D) (selected P G hw pay mounted a.1 a.2)
  let here := (DescentCommonPalette.rotorSiteEquiv G D (selectedRotorLayers P G hw pay mounted s g) C₀ bits (m*p)) v
  change ∃edge,(portMap rack₀ devices₀ (s,.inl g) here).slot ref.port=.inl edge ∧ _
  rw [inner]
  cases s with
  | false=>
    refine ⟨_,rfl,rfl,?_,rfl⟩
    exact (DescentNetworkSubstitution.sourceTap_at rack₀ devices₀ ⟨P.contact e.val,congrArg (Prod.mk false) e.property⟩).trans (congrArg (Sigma.mk _) atSite)
  | true=>
    refine ⟨_,rfl,rfl,?_,rfl⟩
    exact (DescentNetworkSubstitution.targetTap_at rack₀ devices₀ ⟨P.contact e.val,congrArg (Prod.mk true) e.property⟩).trans (congrArg (Sigma.mk _) atSite)



local notation "H₀" => Physical.host G.arcs D (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "tapLeg" => DescentResetGates.tapLegLane D (m*p) P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) base key (m:=m) (p:=p) rfl hp
local notation "backLane" => DescentBatchedRotor.tapLane D m p hp P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) base
variable (vertex : Fin (2^n))
variable (i : Fin (DescentPhysicalSplit.count (Physical.host G.arcs D
  (selectedRotorLayers P G hw pay (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay) s g)
  C₀ bits (m*p)) vertex))
local notation "tapSite" => (sizedSite).symm ⟨vertex,.inr i⟩
local notation "rawTap" => (⟨vertex,.inr i⟩ : (trueDevice).Site)
local notation "tapWidth" => boundaryWidth trueDevice rawTap
local notation "tapUnits" => (fun e=>tapWidth e/p)
local notation "gate" t:arg => (mountedGoodNode P G hw pay hardware key D m p hp fit s g tapSite).symm (.inr t)


local notation "leg" => DescentResetGates.legLane (K:=K) D (m*p) P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) base key (m:=m) (p:=p) rfl hp
local notation "pub" => DescentResetGates.publicTapLane D (m*p) P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) base key (m:=m) (p:=p) rfl hp
local notation "legBits_" => @DescentResetGates.legBits (Cells P s g) K itemEnum _ D (m*p) n h bits C₀ G hw pay _ _ base
local notation "color" => DescentLaneGates.Block (selectedRotorLayers P G hw pay sizedHardware s g) m
  (@DescentResetGates.tapBits (Cells P s g) K itemEnum _ D (m*p) n h bits C₀ G hw pay _ _ base vertex i)

private theorem cast_leg (q socket : Leg (P:=Physical.Pin (2^n)) H₀) (same : q=socket) (atTap : tap H₀ q=⟨vertex,.inr i⟩)
    (z : Fin (legBits_ q)) (layer : Fin (selectedRotorLayers P G hw pay sizedHardware s g)) (batch : Fin m) :
    Eq.ndrec (motive := fun t => LaneSource p (boundaryWidth trueDevice t))
      (leg q layer batch z) atTap =
    Eq.ndrec (motive := fun t => LaneSource p (boundaryWidth trueDevice t))
      (leg socket layer batch (z.cast (congrArg legBits_ same))) ((congrArg (tap H₀) same).symm.trans atTap) :=by
  cases same; rfl

private theorem move_wire {X : Type} {B : X→Type} {w : (x:X)→B x→ℕ} {a b : X}
    (same : a=b) (l : Lane p (w a)) :
    Eq.ndrec (motive := fun t => LaneSource p (w t)) (.wire l) same =
      .wire (Eq.ndrec (motive := fun t => Lane p (w t)) l same) := by cases same; rfl

/-- The same physical tap entry reads either polarity from its back-lane
prefix and the actual within-lane offset. -/
theorem installed_focus_tap (q : Fin (2^n)) (pin : Bool) (slot : name H₀ vertex i=.inl (q,pin))
    (t : color)
    (target : ∀z,boundaryWidth bank (venue tapSite) z=boundaryWidth bank (venue tapSite) z/p*p)
    (source : ∀z,tapWidth z=tapUnits z*p)
    (l : Lane p (boundaryWidth trueDevice (tap H₀ (.inl (q,pin)))))
    (issued : pub pin q t.1 t.2.1 (t.2.2.cast (congrArg legBits_ slot))=.wire l)
    (within : ℕ) (covered : within<l.count (fun z=>boundaryWidth trueDevice (tap H₀ (.inl (q,pin))) z/p)) :
    let placed:=(congrArg (tap H₀) slot).symm.trans (tap_named H₀ vertex i)
    let atGate:=Eq.ndrec (motive:=fun a=>(Lane p (boundaryWidth trueDevice a))) l placed
    let back:=backLane vertex i true ⟨i,t⟩
    ∃ref : BlockRef p tapWidth,ref.port=atGate.port ∧ ref.block=l.bundleStart+within ∧
      ((ofProgram (fun z=>boundaryWidth bank (venue tapSite) z/p) target hp (prg (venue tapSite))).keys (gate t))[back.count tapUnits+within]?=some (.inl ((mountedGoodPorts P G hw pay hardware D m p fit s g tapSite).wordBlock ref)) :=by
  intro placed atGate back
  have mark : tapLeg vertex i t.1 t.2.1 t.2.2=.wire atGate :=by
    change Eq.ndrec (motive:=fun a=>LaneSource p (boundaryWidth trueDevice a)) (leg (name H₀ vertex i) t.1 t.2.1 t.2.2) (tap_named H₀ vertex i)=_
    refine (cast_leg P G hw pay hardware key D m p hp fit s g vertex i _ _ slot (tap_named H₀ vertex i) t.2.2 t.1 t.2.1).trans ?_
    change Eq.ndrec (motive:=fun a=>LaneSource p (boundaryWidth trueDevice a)) (pub pin q t.1 t.2.1 (t.2.2.cast (congrArg legBits_ slot))) placed=_
    rw [issued]
    exact move_wire (w:=boundaryWidth trueDevice) p placed l
  have invariant (a b : (trueDevice).Site) (eqn : a=b) (lane : Lane p (boundaryWidth trueDevice a)) :
      let atGate:=(eqn ▸ lane : Lane p (boundaryWidth trueDevice b))
      atGate.count (fun z=>boundaryWidth trueDevice b z/p)=lane.count (fun z=>boundaryWidth trueDevice a z/p) ∧
        atGate.bundleStart=lane.bundleStart :=by cases eqn; exact ⟨rfl,rfl⟩
  obtain ⟨span,first⟩:=invariant _ _ placed l
  let withinSlot : Fin (atGate.count tapUnits) :=⟨within,span.symm ▸ covered⟩
  let ref:=laneBlock tapUnits source hp atGate withinSlot
  exact ⟨ref,rfl,congrArg (·+within) first,installedKnownTap P G hw pay hardware key D m p hp fit s g vertex i
    t target source atGate mark withinSlot⟩


local instance (priority := high) mountedCellsEnum : Fintype (Cells P s g) := itemEnum

open DescentResetLaneIssue DescentRotorOperandQueryROM.Shape DescentResetPublicOperandBook
local notation "cells_" => Cells P s g
local notation "src_" => fun e : cells_=>(head P s g) (DescentRouterSlots.root P.contact P.input P.site P.owner s (.inl g) P.align e)
local notation "dst_" => fun e : cells_=>(tail P s g) (DescentRouterSlots.link P.contact P.owner s (.inl g) e)
local notation "key_" => (Function.Embedding.subtype (fun e=>P.owner s (P.contact e)=.inl g)).trans key
local notation "addr_" => DescentRotor.Ordered.orderedAddress key_ src_ dst_ hw
local notation "prior_" q:arg t:arg j:arg off:arg e:arg => Config.earlierCount src_ dst_ key_
  (⟨true,q,(t).1.val,(t).2.1.val,(j).val,off⟩ : Mouth n) e
local notation "amount_" q:arg => Fintype.card (DescentRotorOperandRanks.At src_ dst_ (fun z=>(if true then z.2 else z.1)=q))*m

/-- The live positive public operand returns the same contact and positive
face on every covered word.  The exact word is absolute in its contact
fibre and may belong to a later original grain than the mouth's owner. -/
theorem installed_contact_tap (q : Fin (2^n)) (slot : name H₀ vertex i=.inl (q,true))
    (t : color) (offset : ℕ) (item : cells_)
    (target : ∀z,boundaryWidth bank (venue tapSite) z=boundaryWidth bank (venue tapSite) z/p*p)
    (source : ∀z,tapWidth z=tapUnits z*p)
    (selected : dst_ item=q ∧ (base).choose (addr_ item).1=t.1 ∧
      (addr_ item).2=t.2.2.cast (congrArg legBits_ slot))
    (covered : offset< min 2 (amount_ q-(prior_ q t (t.2.2.cast (congrArg legBits_ slot)) offset item*m+t.2.1.val))) :
    let absolute:=prior_ q t (t.2.2.cast (congrArg legBits_ slot)) offset item*m+t.2.1.val+offset
    let back:=backLane vertex i true ⟨i,t⟩
    ∃(ref : BlockRef p (boundaryWidth bank (venue tapSite))) (e : Incident bank (venue tapSite)),
      ((ofProgram (fun z=>boundaryWidth bank (venue tapSite) z/p) target hp (prg (venue tapSite))).keys
        (gate t))[back.count tapUnits+offset]?=some (.inl ref) ∧
      ref.port=.inl e ∧ ref.block=absolute ∧ e.val=.inl (P.contact item.val) ∧
      (if s then (bank).dst e.val else (bank).src e.val)=venue tapSite :=by
  intro absolute back
  let digit:=t.2.2.cast (congrArg legBits_ slot)
  obtain ⟨l,atSite,issued,inner⟩:=public_contact_lane D m p hp P.contact P.input P.site P.owner P.align s
    (.inl g) G (head P s g) (tail P s g) base key q t.1 t.2.1 digit item selected
  obtain ⟨firstWord,span⟩:=public_focus_word D m p hp P.contact P.input P.site P.owner P.align s (.inl g)
    G (head P s g) (tail P s g) base key true q t.1 t.2.1 digit offset item selected l issued
  have inRange : offset<l.count (fun z=>boundaryWidth trueDevice (tap H₀ (.inl (q,true))) z/p):=span.symm ▸ covered
  have moved:=installed_focus_tap P G hw pay hardware key D m p hp fit s g vertex i q true slot t target source l issued
    offset inRange
  obtain ⟨ref,atGate,word,read⟩:=moved
  let placed:=(congrArg (tap H₀) slot).symm.trans (tap_named H₀ vertex i)
  have movePort (a b : (trueDevice).Site) (eqn:a=b) (lane:Lane p (boundaryWidth trueDevice a))
      (link_ : _) (atA : (trueDevice).attach link_=a) (here : lane.port=.inr ⟨link_,atA⟩) :
      (eqn ▸ lane : Lane p (boundaryWidth trueDevice b)).port=.inr ⟨link_,atA.trans eqn⟩ :=by
    cases eqn; exact here
  have innerAt:=atGate.trans (movePort _ _ placed l _ atSite inner)
  obtain ⟨edge,port,identity,ending,block⟩:=mountedGood_contact P G hw pay hardware D m p fit s g tapSite item
    ref (atSite.trans placed) innerAt
  refine ⟨_,edge,read,port,block.trans (word.trans (congrArg (·+offset) firstWord)),identity,ending⟩


end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1150000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
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
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite



open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
local notation "where_" x:arg => resetOrigin B hp whole a x

open DescentLaneGates

open DescentPhysicalSplit DescentBundleHistory DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape
variable (side : Bool) (root : B.reset.placement.Good)
local notation "R_" => B.reset.placement
local notation "bits_" => B.reset.width
local notation "sizedHardware" => (splitEq ▸ B.reset.circuit :
  Hardware (K:=F) (C₀:=C) (u:=unit*p) R_ B.reset.graph B.reset.positive B.reset.pay)
local notation "itemEnum" => @Subtype.fintype _ (fun e => (R_).owner side ((R_).contact e) = Sum.inl root)
  (fun _ => Classical.propDecidable _) inferInstance
local instance (priority := high) mountedWindowCellEnum : Fintype (Cells B.reset.placement side root) := itemEnum
local notation "base" => (transportCircuit (b:=itemEnum) (G:=B.reset.graph) (hw:=B.reset.positive) (pay:=B.reset.pay) (sizedHardware side root))
local notation "layers_" => selectedRotorLayers R_ B.reset.graph B.reset.positive B.reset.pay sizedHardware side root
local notation "H₀" => Physical.host B.reset.graph.arcs d layers_ C bits_ (unit*p)
local notation "sizedChoice" => selected R_ B.reset.graph B.reset.positive B.reset.pay sizedHardware side (.inl root)
local notation "trueDevice" => DescentMixedRouter.device B.reset.graph B.reset.positive (unit*p)
  (R_).contact (R_).input (R_).site (R_).owner (R_).align (D:=d) sizedChoice
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv B.reset.graph d layers_ C bits_ (unit*p)
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv B.reset.graph d
  (selectedRotorLayers R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit side root) C bits_ B.reset.unit
local notation "src_" => (fun e : Cells R_ side root=>(DescentChosenRouter.head R_ side root) (DescentRouterSlots.root (R_).contact
  (R_).input (R_).site (R_).owner side (.inl root) (R_).align e))
local notation "dst_" => (fun e : Cells R_ side root=>(DescentChosenRouter.tail R_ side root) (DescentRouterSlots.link (R_).contact (R_).owner side (.inl root) e))
local notation "key_" => (Function.Embedding.subtype (fun e=>(R_).owner side ((R_).contact e)=.inl root)).trans birth
local notation "addr_" => DescentRotor.Ordered.orderedAddress key_ src_ dst_ B.reset.positive
local notation "legBits_" => @DescentResetGates.legBits (Cells R_ side root) F itemEnum _ d (unit*p) B.reset.n h bits_ C B.reset.graph B.reset.positive B.reset.pay _ _ base
variable (vertex : Fin (2^B.reset.n))
variable (i₀ : Fin (DescentPhysicalSplit.count (Physical.host B.reset.graph.arcs d
  (selectedRotorLayers B.reset.placement B.reset.graph B.reset.positive B.reset.pay
    (((Nat.div_mul_cancel whole).symm : B.reset.unit = (B.reset.unit / p) * p) ▸ B.reset.circuit :
      Hardware (K:=F) (C₀:=C) (u:=(B.reset.unit/p)*p) B.reset.placement B.reset.graph B.reset.positive B.reset.pay) side root)
    C B.reset.width ((B.reset.unit/p)*p)) vertex))
local notation "rawTap" => (⟨vertex,.inr i₀⟩ : (trueDevice).Site)
local notation "site_" => ((sizedSite).symm rawTap)
local notation "venue_" => (⟨(side,.inl root),installedSite site_⟩ : B.reset.bank.Site)
local notation "tapWidth" => boundaryWidth trueDevice rawTap
local notation "tapUnits" => (fun k=>tapWidth k/p)
local notation "gate_" t:arg => (mountedGoodNode R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth
  d unit p hp splitEq side root site_).symm (.inr t)
local notation "back_" t:arg => DescentBatchedRotor.tapLane d unit p hp (R_).contact (R_).input (R_).site (R_).owner (R_).align
  side (.inl root) B.reset.graph (DescentChosenRouter.head R_ side root) (DescentChosenRouter.tail R_ side root) base vertex i₀ true ⟨i₀,t⟩
local notation "prior_" q:arg t:arg ix:arg off:arg e:arg => Config.earlierCount src_ dst_ key_
  (⟨true,q,(t).1.val,(t).2.1.val,(ix).val,off⟩ : Mouth B.reset.n) e
local notation "num_" q:arg => Fintype.card (DescentRotorOperandRanks.At src_ dst_ (fun z=>z.2=q))*unit

/-- A selected, covered public contact of the actual installed tap.  Every
quantity in the returned key is an address read from this mounted circuit. -/
theorem good_occupied_contact_socket_key {field query lanes batches nodes args grain : ℕ}
    (q₀ : Fin (2^B.reset.n)) (slot : name H₀ vertex i₀=.inl (q₀,true))
    (t : DescentLaneGates.Block layers_ unit (@DescentResetGates.tapBits (Cells R_ side root) F itemEnum _ d (unit*p) B.reset.n h bits_ C B.reset.graph B.reset.positive B.reset.pay _ _ base vertex i₀))
    (y : NodeOrder.All next_) (origin : where_ y=.inr (.inr ⟨venue_,gate_ t⟩))
    (offset : ℕ) (item : Cells R_ side root)
    (selected : dst_ item=q₀ ∧ (base).choose (addr_ item).1=t.1 ∧
      (addr_ item).2=t.2.2.cast (congrArg legBits_ slot))
    (covered : offset< min 2 (num_ q₀-(prior_ q₀ t (t.2.2.cast (congrArg legBits_ slot)) offset item*unit+t.2.1.val))) :
    let absolute:=prior_ q₀ t (t.2.2.cast (congrArg legBits_ slot)) offset item*unit+t.2.1.val+offset
    let wire:=contactParent B ((R_).contact item.val)
    let host:=if side then (blocks B).dst wire else (blocks B).src wire
    let config:=publicOperandConfig B field query lanes batches unit nodes args grain
    let number:=config.rotorContactAt side cap.placement.cap (B.reset.goodLabel B.terminals root)
      (DescentChosenRouter.target R_ side root item)
    ∃out : PublicSocket B host unit absolute true number,
      keyCable installed (middle_ y) ((back_ t).count tapUnits+offset)=some (out.face.val.1,absolute) ∧
      (if out.face.val.2 then (coarse).graph.dst out.face.val.1 else (coarse).graph.src out.face.val.1)=(hop).symm y.1 :=by
  intro absolute wire host config number
  let ports:=mountedGoodPorts R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit
    d unit p splitEq side root site_
  have target:=B.reset.laneWidth_eq unit p splitEq venue_
  have source (w) : tapWidth w=tapUnits w*p :=by
    have same := ports.sameWidth w
    exact same.trans ((target (ports.slot w)).trans (congrArg (fun t => t/p*p) same.symm))
  have got:=installed_contact_tap R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth
    d unit p hp splitEq side root vertex i₀ q₀ slot t offset item target source selected covered
  obtain ⟨ref,edge,read,port,word,genuine,ending⟩:=got
  have routed:=good_tap_contact_socket_key (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (nodes:=nodes) (args:=args) (grain:=grain) B hp one pos whole wide a sh
    y venue_ (gate_ t) origin ((back_ t).count tapUnits+offset) side root item ref edge port genuine ending read
  change ref.block=absolute at word
  let receipt (j : ℕ) := ∃out : PublicSocket B host unit j true number,
    keyCable installed (middle_ y) ((back_ t).count tapUnits+offset)=some (out.face.val.1,j) ∧
    (if out.face.val.2 then (coarse).graph.dst out.face.val.1 else (coarse).graph.src out.face.val.1)=(hop).symm y.1
  exact Eq.mp (congrArg receipt word) routed

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

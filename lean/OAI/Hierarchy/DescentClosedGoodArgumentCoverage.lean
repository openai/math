import OAI.Hierarchy.DescentClosedPrivateRotorEntry
import OAI.Hierarchy.DescentClosedResetSlotCount
import OAI.Hierarchy.DescentRotorArgumentCoverage
import OAI.Hierarchy.DescentRotorPrivateAddressPrefix

namespace OAI
namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentMixedRouter DescentBatchedBank DescentBatchedNodeOrder DescentKernelHistory DescentBundleHistory DescentRotor
open ThreeFlat LinearAlgebra.SpectralBooks NonlinearExpanders
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {I U R W K : Type} [Fintype I] [Fintype U] [Fintype R] [Fintype W] [Field K]
variable {n h mult num : ℕ} (G : Graph n h) (C : Shape) (D p : ℕ) (hp : 0<p) {hw : 0<C.packet}
variable (contact : I→U) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→U→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin num) {s : Bool} {w : W}
local notation "Ch" => Choice (K:=K) (C₀:=mult) G hw (C.batches*p) contact input site owner align s w
local notation "net" => DescentMixedRouter.device G hw (C.batches*p) contact input site owner align (D:=D)
local notation "pr" => deviceProgram G hw C.batches p hp contact input site owner align key D

def choicePublicArgument : (ch : Ch) → (actor : (net ch).Site) → (pr ch actor).Node → ℕ → Prop
  | .good first last _ chip, actor, node, arg =>
    C.PublicArgument G D p hp contact input site owner align s w first last chip key actor node arg
  | .exceptional _, _, _, _ => False

def choicePrivateArgument : (ch : Ch) → (actor : (net ch).Site) → (pr ch actor).Node → ℕ → Option (PrivateLane G × ℕ)
  | .good first last pay chip, actor, node, arg =>
    let ord := deviceOrder G hw C.batches p hp contact input site owner align key D (.good first last pay chip)
    let bare := DescentCommonPalette.rotorSiteEquiv G D chip.layers mult C.packet (C.batches*p)
    (C.flattened G mult chip.layers p (ord actor node).val (bare.symm actor))[arg]?
  | .exceptional _, _, _, _ => none

omit [Fintype R] in
theorem choice_argument_coverage (ch : Ch) (good : (match ch with | .good .. => True | .exceptional _ => False))
    (actor : (net ch).Site) (node : (pr ch actor).Node)
    (blocks : ∀a, boundaryWidth (net ch) actor a=(boundaryWidth (net ch) actor a/p)*p)
    (arg : ℕ) (live : arg<((ofProgram (fun a=>boundaryWidth (net ch) actor a/p) blocks hp (pr ch actor)).keys node).length) :
    (∃q k,choicePrivateArgument G C D p hp contact input site owner align key ch actor node arg=some (q,k)) ∨
      choicePublicArgument G C D p hp contact input site owner align key ch actor node arg := by
  cases ch with
  | exceptional data => exact good.elim
  | good first last pay chip =>
    exact C.rotor_argument_coverage G D p hp contact input site owner align s w first last chip key actor node blocks arg live

def choicePrivateEdge : (ch : Ch) → (DescentCommonPalette.rotor G).Edge → Option (net ch).Edge
  | .good _ _ _ chip, e => some (DescentCommonPalette.rotorEdgeEquiv G D chip.layers mult C.packet (C.batches*p) e)
  | .exceptional _, _ => none

omit [Fintype R] in
theorem choice_argument_key (ch : Ch) (actor : (net ch).Site) (node : (pr ch actor).Node)
    (blocks : ∀a,boundaryWidth (net ch) actor a=boundaryWidth (net ch) actor a/p*p)
    (arg within : ℕ) (l : PrivateLane G)
    (hit : choicePrivateArgument G C D p hp contact input site owner align key ch actor node arg=some (l,within)) :
    ∃ ref : BlockRef p (boundaryWidth (net ch) actor),
      ((ofProgram (fun a=>boundaryWidth (net ch) actor a/p) blocks hp (pr ch actor)).keys node)[arg]?=some (.inl ref) ∧
      ref.cableNumber (net ch) actor=(choicePrivateEdge G C D p contact input site owner align ch l.edge).map
        (fun e=>(e,l.start/p+within)) := by
  cases ch with
  | exceptional data => contradiction
  | good first last pay chip =>
    exact C.rotor_address_key G D p hp contact input site owner align s w first last chip key actor node
      blocks arg within l hit


end
end Hierarchy.DescentRotorOperandQueryROM.Shape

/-! # The two physical sources of a reached operand in a mounted good reset device -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
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
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite

open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "where_" x:arg => resetOrigin B hp whole a x

open DescentBatchedBank DescentBundleHistory DescentRotor DescentResetLocalRoster
variable (s : Bool) (root : B.reset.placement.Good) (cell : (DescentCommonPalette.rotor B.reset.graph).Site)
local notation "R₀" => B.reset.placement
local notation "sizedHardware" => (splitEq ▸ B.reset.circuit :
  Hardware (K:=F) (C₀:=C) (u:=unit*p) R₀ B.reset.graph B.reset.positive B.reset.pay)
local notation "sizedChoice" => selected R₀ B.reset.graph B.reset.positive B.reset.pay sizedHardware s (.inl root)
local notation "rawDevice" => DescentMixedRouter.device B.reset.graph B.reset.positive (unit*p)
  (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align (D:=d) sizedChoice
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv B.reset.graph d
  (selectedRotorLayers R₀ B.reset.graph B.reset.positive B.reset.pay sizedHardware s root) C B.reset.width (unit*p)
local notation "sizedEdge" => DescentCommonPalette.rotorEdgeEquiv B.reset.graph d
  (selectedRotorLayers R₀ B.reset.graph B.reset.positive B.reset.pay sizedHardware s root) C B.reset.width (unit*p)
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv B.reset.graph d
  (selectedRotorLayers R₀ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit s root) C B.reset.width B.reset.unit
local notation "prog" => DescentBatchedBank.deviceProgram B.reset.graph B.reset.positive unit p hp
  (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align birth d sizedChoice (sizedSite cell)
local notation "mounted" => (⟨(s,.inl root),installedSite cell⟩ : B.reset.bank.Site)
local notation "ports" => mountedGoodPorts R₀ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit d unit p splitEq s root cell
local notation "gate" z:max => (mountedGoodNode R₀ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth d unit p hp splitEq s root cell).symm z
local notation "trueUnits" => fun a=>boundaryWidth rawDevice (sizedSite cell) a/p

open DescentRetainedRangeDigits DescentBatchedNodeOrder

/-- The bank shape supplied by the chosen reset provides the batch and packet widths. -/
def actualRotorChart (template : DescentRotorOperandQueryROM.Shape) : DescentRotorOperandQueryROM.Shape :=
  {template with packet:=B.reset.width,batches:=B.reset.unit/p}

theorem actualRotorChart_eq (template : DescentRotorOperandQueryROM.Shape)
    (packet : template.packet=B.reset.width) (batch : template.batches=B.reset.unit/p) :
    actualRotorChart (p:=p) B template=template :=by
  cases template
  simp_all [actualRotorChart]

variable (template : DescentRotorOperandQueryROM.Shape)
local notation "cfg" => actualRotorChart (p:=p) B template
local notation "ord" => deviceOrder B.reset.graph B.reset.positive unit p hp
  (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align birth d
  sizedChoice
local notation "flat" z:max => DescentRotorOperandQueryROM.Shape.flattened (n:=B.reset.n) (h:=h) B.reset.graph cfg C (selectedRotorLayers R₀ B.reset.graph B.reset.positive B.reset.pay sizedHardware s root) p (ord (sizedSite cell) z).val cell
local notation "publicArg" z:arg j:arg => DescentRotorOperandQueryROM.Shape.choicePublicArgument (K:=F) (mult:=C)
  (hw:=B.reset.positive) B.reset.graph cfg d p hp (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align birth
  sizedChoice (sizedSite cell) z j
local notation "countAt" y:arg => (occurrences ((after_).sites (y).1) (y).2).length
local notation "multiple" => rotor_private_multiple (B:=B) (whole:=whole) (s:=s) (root:=root) (cell:=cell)

/-- Every in-bounds occurrence in the final archive belongs to the private rows or to
the selected connected public socket at precisely the same ordinal. -/
theorem good_argument_coverage (y : NodeOrder.All next_) (localNode : (prog).Node)
    (origin : where_ y=.inr (.inr ⟨mounted,gate localNode⟩)) (slot : Fin (countAt y)) :
    (∃ l within,(flat localNode)[slot.val]?=some (l,within)) ∨ publicArg localNode slot.val :=by
  have stageCount:=device_slot_count B hp one pos whole wide a sh y mounted (gate localNode) origin
  have words:=mountedGoodWords R₀ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth d
    unit p hp splitEq s root cell (B.reset.laneWidth_eq unit p splitEq mounted) multiple (gate localNode)
  rw [Equiv.apply_symm_apply] at words
  have live : slot.val<((ofProgram trueUnits multiple hp prog).keys localNode).length :=
    slot.isLt.trans_eq (stageCount.trans words)
  have covering := DescentRotorOperandQueryROM.Shape.choice_argument_coverage (K:=F) (mult:=C) (hw:=B.reset.positive)
    B.reset.graph cfg d p hp (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align birth sizedChoice
    True.intro (sizedSite cell) localNode multiple slot.val live
  rcases covering with ⟨l,within,hit⟩ | extArg
  · refine Or.inl ⟨l,within,?_⟩
    exact (congrArg (fun v => (DescentRotorOperandQueryROM.Shape.flattened (n:=B.reset.n) (h:=h)
      B.reset.graph cfg C (selectedRotorLayers R₀ B.reset.graph B.reset.positive B.reset.pay sizedHardware s root)
      p (ord (sizedSite cell) localNode).val v)[slot.val]?) ((sizedSite).symm_apply_apply cell)).symm.trans hit
  · exact Or.inr extArg


/-- A private operand names the installed cable and its exact word at the reached
site. A public operand retains its actual connected socket and bounded lane word. -/
theorem good_argument_entry (y : NodeOrder.All next_) (localNode : (prog).Node)
    (origin : (where_ y)=Sum.inr (.inr ⟨mounted,gate localNode⟩)) (slot : Fin (countAt y)) :
    (∃ (l : DescentRotorOperandQueryROM.Shape.PrivateLane B.reset.graph) (within : ℕ),
      (flat localNode)[slot.val]?=some (l,within) ∧
      (hop).symm y.1=B.reset.rotorSiteAt B.terminals s root cell ∧
      ∃ (e : Incident (coarse).graph ((hop).symm y.1)) (fit : (l.start/p+within+1)*p≤(coarse).graph.width e.val),
        e.val=privateWire B (goodOccurrence B s root l.edge) ∧
        (((installed).sites ((hop).symm y.1)).keys y.2)[slot.val]?=
          some (.inl ⟨.inl e,l.start/p+within,fit⟩)) ∨ publicArg localNode slot.val :=by
  rcases good_argument_coverage B hp one pos whole wide a sh s root cell template y localNode origin slot with
    ⟨l,within,hit⟩|outside
  · have chosen : DescentRotorOperandQueryROM.Shape.choicePrivateArgument (n:=B.reset.n) (h:=h)
        B.reset.graph cfg d p hp (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align birth
        sizedChoice (sizedSite cell) localNode slot.val=some (l,within) := by
      change (DescentRotorOperandQueryROM.Shape.flattened (n:=B.reset.n) (h:=h) B.reset.graph cfg C
        (selectedRotorLayers R₀ B.reset.graph B.reset.positive B.reset.pay sizedHardware s root) p
        (ord (sizedSite cell) localNode).val ((sizedSite).symm (sizedSite cell)))[slot.val]?=_
      rw [Equiv.symm_apply_apply]
      exact hit
    obtain ⟨ref,found,ident⟩:=DescentRotorOperandQueryROM.Shape.choice_argument_key (n:=B.reset.n) (h:=h)
      B.reset.graph cfg d p hp (R₀).contact (R₀).input (R₀).site (R₀).owner (R₀).align birth
      sizedChoice (sizedSite cell) localNode multiple slot.val within l chosen
    have reached:=device_private_rotor_entry B hp one pos whole wide a sh s root cell y localNode origin
      slot.val l.edge (l.start/p+within) multiple ref found ident
    exact Or.inl ⟨l,within,hit,reached.1,reached.2⟩
  · exact Or.inr outside

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

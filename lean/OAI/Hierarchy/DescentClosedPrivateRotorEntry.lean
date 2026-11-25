import OAI.Hierarchy.DescentClosedFreshArgumentKeys
import OAI.Hierarchy.DescentMountedPrivateWire
import OAI.Hierarchy.DescentResetOriginalOperandSite
import OAI.Hierarchy.DescentInstalledRotorCandidate

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1150000
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

theorem rotor_private_multiple (a) : boundaryWidth rawDevice (sizedSite cell) a=trueUnits a*p :=by
  have same := (ports).sameWidth a
  exact same.trans ((B.reset.laneWidth_eq unit p splitEq mounted ((ports).slot a)).trans
    (congrArg (fun w => w/p*p) same.symm))

/-- The actual original rotor cable and its p-word in the installed archive
of a genuine reset, including both the occupied site and its argument. -/
theorem device_private_rotor_entry (y : NodeOrder.All next_) (localNode : (prog).Node)
    (origin : (where_ y)=Sum.inr (.inr ⟨mounted,gate localNode⟩)) (arg : ℕ)
    (edge : (DescentCommonPalette.rotor B.reset.graph).Edge) (word : ℕ)
    (source : ∀a,boundaryWidth rawDevice (sizedSite cell) a=trueUnits a*p)
    (ref : BlockRef p (boundaryWidth rawDevice (sizedSite cell)))
    (found : ((ofProgram trueUnits source hp prog).keys localNode)[arg]?=some (.inl ref))
    (identity : ref.cableNumber rawDevice (sizedSite cell)=some (sizedEdge edge,word)) :
    (hop).symm y.1=B.reset.rotorSiteAt B.terminals s root cell ∧
    ∃ (e : Incident (coarse).graph ((hop).symm y.1)) (fit : (word+1)*p≤(coarse).graph.width e.val), e.val=privateWire B (goodOccurrence B s root edge) ∧
      (((installed).sites ((hop).symm y.1)).keys y.2)[arg]?=some (.inl ⟨.inl e,word,fit⟩) :=by
  have atSite:=device_original_site B hp whole a y mounted (gate localNode) origin
  refine ⟨atSite,?_⟩
  obtain ⟨wire,valid,named,read⟩:=mountedGoodPrivateKey R₀ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit
    birth d unit p hp splitEq s root cell source (B.reset.laneWidth_eq unit p splitEq mounted) localNode
    arg ref edge word found identity
  have posted:=device_installed_wire B hp one pos whole wide a sh y mounted (gate localNode) origin arg word wire valid read
  rw [named] at posted
  exact keyCable_entry installed (middle_ y) arg (privateWire B (goodOccurrence B s root edge)) word posted

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

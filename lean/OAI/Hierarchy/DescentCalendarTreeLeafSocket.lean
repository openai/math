import OAI.Hierarchy.DescentInstalledTreeLeafKey
import OAI.Hierarchy.DescentFallbackRootSocket
import OAI.Hierarchy.DescentFreshTreeRange

namespace OAI
/-! The issued exceptional leaf word points to the actual direct contact at either endpoint. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentKernelHistory DescentLaneGates DescentBundleHistory DescentChosenRouter
open DescentContactTree DescentRouterSlots DescentTreePrefixIntervals DescentCompiler DescentResetGates
open DescentResetLocalRoster DescentResetCableSlots DescentColonies
open DescentLaneGates DescentBundleHistory DescentFallbackItemSelect DescentTreeLaneProgram
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000

variable {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => (Z).placement
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "ht" => GroupStage.depthBound D n f g
variable {p split : ℕ} (hp : 0 < p) (unitFit : B.reset.unit=split*p)
  (s : Bool) (t : B.reset.Fallback) (e : DescentRouterSlots.Item B.reset.placement.contact B.reset.placement.owner s (.inr t))
  (b : Fin split)
local notation "bk" => (placement).fallbackBook s t
local notation "linkAt" => link (placement).contact (placement).owner s (.inr t)
local notation "code" => DescentFixedNamedContact.code (bk).codes linkAt
local notation "leaf" => (bk).codes (linkAt e)
local notation "prefix_" => prefixAt code (bk).height e
local notation "node" => (⟨Fin.last (bk).height,prefix_⟩ : Physical.Site (bk).height)
local notation "venue" => (⟨(s,.inr t),node⟩ : (Z).bank.Site)
local notation "gate" => installedTreeGate (K:=F) (C₀:=C) (k:=B.reset.k) (n:=B.reset.n) (h:=h) (bits:=B.reset.width) (u:=B.reset.unit) (N:=∑ x,B.count x) placement (Z).graph (Z).positive (Z).pay (Z).circuit birth
  d split p hp unitFit s t node ⟨e,rfl⟩ b
local notation "raw" => DescentFixedExceptionalRouter.device d (placement).contact (placement).input
  (placement).site (placement).owner (fun _ : (W.granular B.count (z*G.b) B.fit).graph.Edge => split*p) s (.inr t) (bk).codes
local notation "op" => (DescentTreeLaneProgram.program d (placement).contact (placement).input (placement).site
  (placement).owner (placement).align split p hp s (.inr t) (bk).codes birth (2^(Z).n) node).op (⟨e,rfl⟩,b)
local notation "units" => (fun a=>boundaryWidth raw node a/p)
local notation "left" => (op).arg (0 : Fin 2)
local notation "right" => (op).arg (1 : Fin 2)
local notation "wire" => contactParent B ((placement).contact e.val)
local notation "host" => if s then (blocks B).dst wire else (blocks B).src wire
variable {field query lanes nodes args grain : ℕ}
local notation "cfg" => flatConfig B field query lanes split split nodes args
local notation "pubCfg" => publicOperandConfig B field query lanes split split nodes args grain
local notation "root" => ((Z).fallLabel T t,((T).code t).2.2)
local notation "adult" => (Z).laneShape birth split p hp unitFit venue
local notation "mul" => word_multiple d (placement).contact (placement).input (placement).site (placement).owner
  pubCfg p s (.inr t) (bk).codes node

private theorem leaf_earlier_count {α : Type} (ports : Fin 2→α) (weight : α→ℕ) :
    (((List.ofFn ports).take 1).map weight).sum=weight (ports 0) := by
  rw [List.ofFn_succ]
  simp

/-- The original leaf-side block is a wire of the substituted bank, carrying
the original contact's local word number. -/
def tree_leaf_keyed_socket (xs : Fin (cfg).count→DescentFallbackItemSelect.Item)
    (j : Fin ((right).count units)) :
    let a:=(left).count units
    let word:=(right).bundleStart+j.val
    let number:=(cfg).contactAt s input.placement.cap (bk).height (start ht leaf) root
    let r:=laneBlock units mul hp right j
    let ref:=((Z).treePorts split p unitFit s t node).wordBlock r
    Σ' socket : PublicSocket B host split word true number,
      (cfg).physicalReply s input.placement.cap (bk).height (List.ofFn prefix_) root xs (start ht leaf)
        left right (a+j.val)=some (number,word,(right).count units,true) ∧
      ((adult).keys gate)[a+j.val]?=some (.inl ref) ∧
      deviceRoute B hp venue ref=(socket.face.val.1,word) ∧ socket.face.val=(wire,s) :=by
  intro a word number r ref
  obtain ⟨found,coordinate,valid⟩:=installed_leaf_block (K:=F) (C₀:=C) (k:=B.reset.k) (n:=B.reset.n) (h:=h) (bits:=B.reset.width) (u:=B.reset.unit) (N:=∑ x,B.count x) placement (Z).graph (Z).positive (Z).pay
    (Z).circuit birth d split p hp unitFit s t e b mul j
  have inRange : word/split<Fintype.card (DescentNamedContact.Fibre (placement).contact ((placement).contact e.val)):=by
    simpa only [coordinate] using valid
  let socket:=reached_leaf_socket (field:=field) (query:=query) (lanes:=lanes) (batches:=split)
    (nodes:=nodes) (args:=args) B s t e word inRange
  refine ⟨socket,?_,?_,?_,rfl⟩
  · simp [DescentFallbackOperandBranch.Config.physicalReply,a,word,number,j.isLt]
  · have hit:=(Z).tree_gate_lanes birth split p hp unitFit s t node ⟨e,rfl⟩ b mul (1 : Fin 2) j
    have before := leaf_earlier_count (op).arg (fun l => l.count units)
    exact (congrArg (fun u : ℕ => ((adult).keys gate)[u+j.val]?) before.symm).trans hit
  · change deviceRoute B hp venue ref=(wire,word)
    have routed (r₀ : BlockRef p (boundaryWidth (Z).bank venue))
        (atWire : Sum.map Subtype.val Subtype.val r₀.port=.inl (.inl ((placement).contact e.val))) :
        deviceRoute B hp venue r₀=(wire,r₀.block) :=by
      rcases r₀ with ⟨edge|sock,i,hi⟩
      · have key : edge.val=.inl ((placement).contact e.val):=Sum.inl.inj atWire
        change ((motherNames B).symm (.inr (.inr edge.val)),i)=_
        rw [key]
        rfl
      · cases atWire
    exact (routed ref found).trans (congrArg (Prod.mk wire) coordinate)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

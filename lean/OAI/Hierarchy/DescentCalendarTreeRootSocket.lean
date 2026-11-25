import OAI.Hierarchy.DescentFallbackRootSocket
import OAI.Hierarchy.DescentNumberedFallbackKeys
import OAI.Hierarchy.DescentFreshTreeRange

namespace OAI
/-! # The original left tree argument through the installed key and socket -/
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentContactTree DescentRouterSlots DescentOrderedWords DescentBatchedBank DescentLaneGates
open DescentBundleHistory DescentNetworkSubstitution
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
variable {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
  (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
  (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "selection" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align selection D
variable (s : Bool) (t : H)
local notation "book" => P.fallbackBook s t
local notation "code" => DescentFixedNamedContact.code (book).codes (link P.contact P.owner s (.inr t))
local notation "venue" q => (⟨(s,.inr t),q⟩ : (bank).Site)

variable (e : Item P.contact P.owner s (.inr t)) (b : Fin m)
local notation "q₀" => (⟨0,prefixAt code 0 e⟩ : Physical.Site (book).height)


local notation "dstLane" => installedRootLane P G hw pay hardware key D m p hp fit s t e b
local notation "raw" => DescentFixedExceptionalRouter.device D P.contact P.input P.site P.owner
  (fun _ : I=>m*p) s (.inr t) (book).codes
local notation "sourceOp" => (DescentTreeLaneProgram.program D P.contact P.input P.site P.owner P.align
  m p hp s (.inr t) (book).codes key (2^n) q₀).op (⟨e,rfl⟩,b)
local notation "srcLane" => (sourceOp).arg (0 : Fin 2)

theorem installed_root_measure :
    (dstLane).count (fun a=>boundaryWidth bank (venue q₀) a/p)=
      (srcLane).count (fun a=>boundaryWidth raw q₀ a/p) ∧ (dstLane).bundleStart=(srcLane).bundleStart :=by
  subst u
  let rack:=DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I=>m*p)
  let devices:=fun a : rack.Site=>DescentMixedRouter.device (K:=K) (C₀:=C₀) G hw (m*p) P.contact P.input P.site P.owner P.align
    (D:=D) (selected P G hw pay hardware a.1 a.2)
  exact ⟨(portMap rack devices (s,.inr t) q₀).lane_count srcLane,rfl⟩

theorem installed_root_block
    (target : ∀a,boundaryWidth bank (venue q₀) a=boundaryWidth bank (venue q₀) a/p*p)
    (source : ∀a,boundaryWidth raw q₀ a=boundaryWidth raw q₀ a/p*p)
    (j : Fin ((srcLane).count (fun a=>boundaryWidth raw q₀ a/p))) :
    laneBlock (fun a=>boundaryWidth bank (venue q₀) a/p) target hp dstLane
      (j.cast (installed_root_measure P G hw pay hardware key D m p hp fit s t e b).1.symm)=
      (installedTreePorts P G hw pay hardware D m p fit s t q₀).wordBlock
        (laneBlock (fun a=>boundaryWidth raw q₀ a/p) source hp srcLane j) :=by
  subst u
  rfl
end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentFallbackOperandBranch.Config
open DescentFallbackItemSelect DescentResetLocalRoster DescentLaneGates
private theorem rootReply_congr {n p : ℕ} (cfg : DescentFallbackOperandBranch.Config)
    (side : Bool) (cap depth : ℕ) (root : code cfg.residual × Option (Fin (2^n)))
    (items : Fin cfg.count → Item) (leaf index : ℕ) {Q Q' : Type}
    {width : Q → ℕ} {width' : Q' → ℕ}
    (l r : Lane p width) (l' r' : Lane p width')
    (bound : index < l.count (fun a => width a / p))
    (sameCount : l.count (fun a => width a / p) = l'.count (fun a => width' a / p))
    (sameStart : l.bundleStart = l'.bundleStart) :
    cfg.physicalReply side cap depth [] root items leaf l r index =
    cfg.physicalReply side cap depth [] root items leaf l' r' index := by
  have bound' : index < l'.count (fun a => width' a / p) := sameCount ▸ bound
  simp only [physicalReply, sameCount, sameStart, ite_eq_left bound']
end Hierarchy.DescentFallbackOperandBranch.Config

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentKernelHistory DescentLaneGates DescentBundleHistory DescentChosenRouter
open DescentContactTree DescentRouterSlots DescentTreePrefixIntervals DescentCompiler DescentResetGates
open DescentResetLocalRoster DescentResetCableSlots DescentColonies
open DescentLaneGates DescentBundleHistory DescentFallbackItemSelect DescentTreeLaneProgram
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

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
  (s : Bool) (t : B.reset.Fallback) (e : Item B.reset.placement.contact B.reset.placement.owner s (.inr t))
  (b : Fin split)
local notation "bk" => (placement).fallbackBook s t
local notation "linkAt" => link (placement).contact (placement).owner s (.inr t)
local notation "code" => DescentFixedNamedContact.code (bk).codes linkAt
local notation "leaf" => (bk).codes (linkAt e)
local notation "prefix_" => prefixAt code 0 e
local notation "node" => (⟨0,prefix_⟩ : Physical.Site (bk).height)
local notation "venue" => (⟨(s,.inr t),node⟩ : (Z).bank.Site)
local notation "gate" => installedTreeGate placement (Z).graph (Z).positive (Z).pay (Z).circuit birth
  d split p hp unitFit s t node ⟨e,rfl⟩ b
local notation "raw" => DescentFixedExceptionalRouter.device d (placement).contact (placement).input
  (placement).site (placement).owner (fun _=>split*p) s (.inr t) (bk).codes
local notation "op" => (DescentTreeLaneProgram.program d (placement).contact (placement).input (placement).site
  (placement).owner (placement).align split p hp s (.inr t) (bk).codes birth (2^(Z).n) node).op (⟨e,rfl⟩,b)
local notation "units" => (fun a=>boundaryWidth raw node a/p)
local notation "left" => (op).arg (0 : Fin 2)
local notation "right" => (op).arg (1 : Fin 2)
local notation "wire" => contactParent B ((placement).contact e.val)
local notation "host" => if s then (blocks B).dst wire else (blocks B).src wire
variable {field query lanes nodes args : ℕ}
local notation "cfg" => flatConfig B field query lanes split split nodes args
local notation "pubCfg" => publicOperandConfig B field query lanes split split nodes args p
local notation "root" => ((Z).fallLabel T t,((T).code t).2.2)
local notation "adult" => (Z).laneShape birth split p hp unitFit venue
local notation "mul" => word_multiple d (placement).contact (placement).input (placement).site (placement).owner
  pubCfg p s (.inr t) (bk).codes node


local notation "realLeft" => (Z).rootLane birth split p hp unitFit s t e b
local notation "bankUnits" => (fun a=>boundaryWidth (Z).bank venue a/p)

set_option maxHeartbeats 1200000 in
/-- The reference indexed in the original gate and the actual outgoing root
query both name this signed stem, also for a word in the next sorted grain. -/
def tree_root_keyed_socket (xs : Fin (cfg).count→DescentFallbackItemSelect.Item)
    (read : RootRows B s ((placement).input s e.val) xs) (j : Fin ((left).count units)) :
    let word:=(left).bundleStart+j.val
    let r:=laneBlock units mul hp left j
    let ref:=((Z).treePorts split p unitFit s t node).wordBlock r
    Σ' (number : ℕ) (socket : PublicSocket B (treeReceiver B venue) split (word%split) false number),
      (cfg).physicalReply s input.placement.cap (bk).height (List.ofFn prefix_) root xs (start ht leaf)
        left right j.val=some (number,word%split,(left).count units,false) ∧
      ((adult).keys gate)[j.val]?=some (.inl ref) ∧ deviceRoute B hp venue ref=(socket.face.val.1,word%split) :=by
  intro word r ref
  have measure:=installed_root_measure placement (Z).graph (Z).positive (Z).pay (Z).circuit
    birth d split p hp unitFit s t e b
  let actualJ : Fin ((realLeft).count bankUnits):=j.cast measure.1.symm
  let issued:=tree_root_socket B hp unitFit s t e b xs read realLeft (start ht leaf) actualJ
  let number:=Classical.choose issued
  have available:=Classical.choose_spec issued
  let sock:=Classical.choose available
  have correct:=Classical.choose_spec available
  have startEq : (realLeft).bundleStart+actualJ.val=word:=congrArg (·+j.val) measure.2
  let picked : PublicSocket B (treeReceiver B venue) split (word%split) false number:=
    ⟨sock.face,sock.address,by simpa only [startEq] using sock.inside,
      by simpa only [startEq] using sock.mark⟩
  refine ⟨number,picked,?_,?_,?_⟩
  · have countEq : (realLeft).count bankUnits = (left).count units := measure.1
    have mapReply := DescentFallbackOperandBranch.Config.rootReply_congr (cfg) s input.placement.cap
      (bk).height root xs (start ht leaf) j.val left right realLeft realLeft j.isLt countEq.symm measure.2.symm
    have readReply : (cfg).physicalReply s input.placement.cap (bk).height [] root xs (start ht leaf)
        realLeft realLeft actualJ.val = some (number,((realLeft).bundleStart+actualJ.val)%split,
          (realLeft).count bankUnits,false) := correct.1
    have sameAnswer := congrArg₂ (fun origin count : ℕ =>
      some (number,origin%split,count,false)) startEq countEq
    have sameIndex : j.val = actualJ.val := rfl
    have readIndex := congrArg (fun i => (cfg).physicalReply s input.placement.cap (bk).height []
      root xs (start ht leaf) realLeft realLeft i) sameIndex
    exact mapReply.trans (readIndex.trans (readReply.trans sameAnswer))
  · have keyRead:=(Z).tree_gate_lanes birth split p hp unitFit s t node ⟨e,rfl⟩ b mul (0 : Fin 2) j
    have firstKey : ((adult).keys gate)[0+j.val]? = some (.inl ref) := keyRead
    exact (congrArg (fun i : ℕ => ((adult).keys gate)[i]?) (Nat.zero_add j.val).symm).trans firstKey
  · have blockEq : laneBlock bankUnits ((Z).laneWidth_eq split p unitFit venue) hp realLeft actualJ = ref :=
      installed_root_block placement (Z).graph (Z).positive (Z).pay (Z).circuit birth d split p hp unitFit s t e b
        ((Z).laneWidth_eq split p unitFit venue) mul j
    exact (congrArg (deviceRoute B hp venue) blockEq.symm).trans (by simpa only [picked, sock, startEq] using correct.2)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

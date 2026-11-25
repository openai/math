import OAI.Hierarchy.DescentNumberedFallbackNode
import OAI.Hierarchy.DescentLanePortKeys

namespace OAI
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentContactTree DescentRouterSlots DescentOrderedWords DescentBatchedBank DescentBundleHistory
open DescentRetainedRangeDigits DescentPhysicalSplit
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
variable {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
  (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
  (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "selection" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align selection D
local notation "programAt" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D selection
variable (s : Bool) (t : H)
variable (q : Physical.Site (P.fallbackBook s t).height)
local notation "venue" => (⟨(s,.inr t),q⟩ : (bank).Site)
local notation "raw" => DescentFixedExceptionalRouter.device D P.contact P.input P.site P.owner (fun _ : I=>m*p) s (Sum.inr t) (P.fallbackBook s t).codes
local notation "rawOp" => DescentTreeLaneProgram.program D P.contact P.input P.site P.owner P.align m p hp s (Sum.inr t) (P.fallbackBook s t).codes key (2^n) q
variable (e : Cell (DescentFixedNamedContact.code (P.fallbackBook s t).codes
    (link P.contact P.owner s (Sum.inr t))) q.1.val q.2) (batch : Fin m)

local notation "gate" => installedTreeGate P G hw pay hardware key D m p hp fit s t q e batch
open DescentLaneGates
include fit in
/-- Port substitution on the actual signed fallback bank after paying the
common unit equality. Its slot is the original physicalPort of the bank. -/
def installedTreePorts : PortMap (boundaryWidth raw q) (boundaryWidth bank venue) :=by
  revert hardware
  subst u
  intro mounted
  let router := DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I => m*p)
  exact DescentBatchedBank.portMap router
    (fun a : router.Site => DescentMixedRouter.device (K:=K) (C₀:=C₀) G hw (m*p)
      P.contact P.input P.site P.owner P.align (D:=D) (selected P G hw pay mounted a.1 a.2))
    (s,Sum.inr t) q

theorem installedTreeKey (mul : ∀a,boundaryWidth bank venue a=boundaryWidth bank venue a/p*p)
    (localMul : ∀a,boundaryWidth raw q a=boundaryWidth raw q a/p*p) (slot : ℕ)
    (r : BlockRef p (boundaryWidth raw q))
    (hit : ((ofProgram (fun a=>boundaryWidth raw q a/p) localMul hp rawOp).keys (e,batch))[slot]?=some (.inl r)) :
    ((ofProgram (fun a=>boundaryWidth bank venue a/p) mul hp (programAt venue)).keys gate)[slot]?=
      some (.inl ((installedTreePorts P G hw pay hardware D m p fit s t q).wordBlock r)) :=by
  subst u
  exact (installedTreePorts P G hw pay hardware D m p rfl s t q).transported_key
    localMul mul hp rawOp (e,batch) slot r hit

theorem installedTreeLength (mul : ∀a,boundaryWidth bank venue a=boundaryWidth bank venue a/p*p)
    (localMul : ∀a,boundaryWidth raw q a=boundaryWidth raw q a/p*p) :
    ((ofProgram (fun a=>boundaryWidth bank venue a/p) mul hp (programAt venue)).keys gate).length=
      ((ofProgram (fun a=>boundaryWidth raw q a/p) localMul hp rawOp).keys (e,batch)).length:=by
  subst u
  exact (congrArg List.length
    ((installedTreePorts P G hw pay hardware D m p rfl s t q).transported_keys
      localMul mul hp rawOp (e,batch))).trans (List.length_map _)

end
end Hierarchy.DescentChosenRouter

namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentChosenRouter DescentOrderedWords DescentContactTree DescentRouterSlots
open DescentKernelHistory DescentRetainedRangeDigits DescentBundleHistory
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
variable {F P : Type} [Field F] {d N : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (key : A.graph.Edge↪Fin N)
variable (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p) (s : Bool) (t : Z.Fallback)
variable (q : Physical.Site (Z.placement.fallbackBook s t).height)
local notation "venue" => (⟨(s,.inr t),q⟩ : Z.bank.Site)
local notation "gate" => installedTreeGate Z.placement Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t q
local notation "raw" => DescentFixedExceptionalRouter.device d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner (fun _ : A.graph.Edge=>m*p) s (Sum.inr t) (Z.placement.fallbackBook s t).codes
local notation "rawOp" => DescentTreeLaneProgram.program d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner Z.placement.align m p hp s (Sum.inr t) (Z.placement.fallbackBook s t).codes key (2^Z.n) q
variable (e : Cell (DescentFixedNamedContact.code (Z.placement.fallbackBook s t).codes
    (link Z.placement.contact Z.placement.owner s (Sum.inr t))) q.1.val q.2) (batch : Fin m)


open DescentLaneGates
include fit in
def treePorts : PortMap (boundaryWidth raw q) (boundaryWidth Z.bank venue) :=
  installedTreePorts Z.placement Z.graph Z.positive Z.pay Z.circuit d m p fit s t q

include fit in
theorem treeMultiple (port) : boundaryWidth raw q port=boundaryWidth raw q port/p*p :=
  before_multiple (Z.treePorts m p fit s t q) (Z.laneWidth_eq m p fit venue) port

/-- The original tree lane's position and within-word offset survive bank
installation, even when its outer port becomes an attached socket. -/
theorem bank_tree_laneBlock (localMul : ∀a,boundaryWidth raw q a=boundaryWidth raw q a/p*p)
    (slot : ℕ) (r : BlockRef p (boundaryWidth raw q))
    (hit : ((ofProgram (fun a=>boundaryWidth raw q a/p) localMul hp rawOp).keys (e,batch))[slot]?=some (.inl r)) :
    ((Z.laneShape key m p hp fit venue).keys (gate e batch))[slot]?=
      some (.inl ((Z.treePorts m p fit s t q).wordBlock r)) :=
  installedTreeKey Z.placement Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t q e batch
    (Z.laneWidth_eq m p fit venue) localMul slot r hit

/-- Obtain the installed cable directly from either original tree argument
and any word covered by its actual stride. -/
theorem tree_gate_lanes (localMul : ∀a,boundaryWidth raw q a=boundaryWidth raw q a/p*p)
    (arg : Fin (((rawOp).op (e,batch)).arity))
    (i : Fin ((((rawOp).op (e,batch)).arg arg).count (fun a=>boundaryWidth raw q a/p))) :
    let earlier:=(List.ofFn ((rawOp).op (e,batch)).arg).take arg.val
    let slot:=(earlier.map (fun l=>l.count (fun a=>boundaryWidth raw q a/p))).sum+i.val
    let original:=laneBlock (fun a=>boundaryWidth raw q a/p) localMul hp (((rawOp).op (e,batch)).arg arg) i
    ((Z.laneShape key m p hp fit venue).keys (gate e batch))[slot]?=
      some (.inl ((Z.treePorts m p fit s t q).wordBlock original)) :=by
  intro earlier slot original
  exact Z.bank_tree_laneBlock key m p hp fit s t q e batch localMul slot original
    (program_key_at (fun a=>boundaryWidth raw q a/p) localMul hp rawOp (e,batch) arg i)

theorem tree_gate_words (localMul : ∀a,boundaryWidth raw q a=boundaryWidth raw q a/p*p) :
    let count:=(fun j : Fin 2=>(((rawOp).op (e,batch)).arg j).count (fun a=>boundaryWidth raw q a/p))
    ((Z.laneShape key m p hp fit venue).keys (gate e batch)).length=count 0+count 1 :=by
  intro count
  refine (installedTreeLength Z.placement Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t q e batch
    (Z.laneWidth_eq m p fit venue) localMul).trans ?_
  refine (congrArg List.length (program_keys (fun a=>boundaryWidth raw q a/p) localMul hp rawOp (e,batch))).trans ?_
  rw [List.length_flatMap]
  change ((List.ofFn (fun j : Fin 2=>((rawOp).op (e,batch)).arg j)).map _).sum=_
  simp [List.ofFn_succ,laneProgramNames,count]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI

import OAI.Hierarchy.DescentInstalledLaneRange
import OAI.Hierarchy.DescentBatchedNodeOrder
import OAI.Hierarchy.DescentTreeLaneAddresses

namespace OAI
/-! # The exception gate in its actual signed bank and physical node order -/
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
local notation "ord" => DescentBatchedNodeOrder.sizedOrder G hw m p hp P.contact P.input P.site P.owner P.align key D u fit selection
variable (s : Bool) (t : H)
local notation "code" => DescentFixedNamedContact.code (P.fallbackBook s t).codes (link P.contact P.owner s (Sum.inr t))
local notation "ids" => DescentOrderedReset.itemKey key P.contact P.owner s (Sum.inr t)
variable (q : Physical.Site (P.fallbackBook s t).height)
local notation "venue" => (⟨(s,.inr t),q⟩ : (bank).Site)
local notation "raw" => DescentFixedExceptionalRouter.device D P.contact P.input P.site P.owner (fun _ : I=>m*p) s (Sum.inr t) (P.fallbackBook s t).codes
local notation "rawOp" => DescentTreeLaneProgram.program D P.contact P.input P.site P.owner P.align m p hp s (Sum.inr t) (P.fallbackBook s t).codes key (2^n) q
variable (e : Cell (DescentFixedNamedContact.code (P.fallbackBook s t).codes
    (link P.contact P.owner s (Sum.inr t))) q.1.val q.2) (batch : Fin m)

include e batch in
def installedTreeGate : (programAt venue).Node :=by
  subst u
  exact (e,batch)

local notation "gate" => installedTreeGate P G hw pay hardware key D m p hp fit s t q e batch

theorem installedTreeIndex : ((ord venue) gate).val=
    (before (Contact.cellKey ids code q.1.val q.2) e).card*m+batch.val :=by
  revert hardware
  subst u
  intro mounted
  rcases q with ⟨level, node⟩
  have number := DescentBatchedNodeOrder.tree_number (K:=K) (C₀:=C₀) (s:=s) (w:=Sum.inr t)
    G hw m p hp P.contact P.input P.site P.owner P.align key D
    ⟨fallback_root (Y:=2^n) P.b P.keys P.hub s t, P.fallbackBook s t⟩ ⟨level,node⟩ e batch
  dsimp only [DescentBatchedNodeOrder.sizedOrder, DescentBatchedNodeOrder.bankOrder,
    installedTreeGate]
  refine number.trans ?_
  apply congrArg (fun cells : Finset (Cell code level.val node) => cells.card*m+batch.val)
  have sameFilter {X : Type} (a b : Fintype X) (left right : X → Prop)
      (dl : DecidablePred left) (dr : DecidablePred right) (agree : ∀ j, left j ↔ right j) :
      @Finset.filter X left dl (@Finset.univ X a) = @Finset.filter X right dr (@Finset.univ X b) := by
    have predicates : left = right := funext fun j => propext (agree j)
    cases predicates
    cases Subsingleton.elim a b
    cases Subsingleton.elim dl dr
    rfl
  unfold before
  apply sameFilter
  intro j
  rfl

theorem installedTreeRange (mul : ∀a,boundaryWidth bank venue a=boundaryWidth bank venue a/p*p)
    (localMul : ∀a,boundaryWidth raw q a=boundaryWidth raw q a/p*p) (slot : ℕ) (field : Fin 3) :
    atSlot (r:=(programAt venue).recipe) (ofProgram (fun a=>boundaryWidth bank venue a/p) mul hp (programAt venue)) gate slot field=
      atSlot (r:=(rawOp).recipe) (ofProgram (fun a=>boundaryWidth raw q a/p) localMul hp rawOp) (e,batch) slot field :=by
  subst u
  exact DescentBatchedBank.installed_range G hw m p hp P.contact P.input P.site P.owner P.align key D
    (selected P G hw pay hardware) ⟨(s,Sum.inr t),q⟩ mul (e,batch) slot field

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
local notation "code" => DescentFixedNamedContact.code (Z.placement.fallbackBook s t).codes (link Z.placement.contact Z.placement.owner s (Sum.inr t))
local notation "ids" => DescentOrderedReset.itemKey key Z.placement.contact Z.placement.owner s (Sum.inr t)
variable (q : Physical.Site (Z.placement.fallbackBook s t).height)
local notation "venue" => (⟨(s,.inr t),q⟩ : Z.bank.Site)
local notation "gate" => installedTreeGate Z.placement Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t q
local notation "raw" => DescentFixedExceptionalRouter.device d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner (fun _ : A.graph.Edge=>m*p) s (Sum.inr t) (Z.placement.fallbackBook s t).codes
local notation "rawOp" => DescentTreeLaneProgram.program d Z.placement.contact Z.placement.input Z.placement.site Z.placement.owner Z.placement.align m p hp s (Sum.inr t) (Z.placement.fallbackBook s t).codes key (2^Z.n) q
variable (e : Cell (DescentFixedNamedContact.code (Z.placement.fallbackBook s t).codes
    (link Z.placement.contact Z.placement.owner s (Sum.inr t))) q.1.val q.2) (batch : Fin m)

include key hp fit e batch in
/-- Physical index in the real reset bank, using the existing local port-load allowance. -/
def numberedTreeGate {nodes : ℕ} (budget : (2*DescentNetworkSubstitution.portLoad Z.bank venue)/p≤nodes) : Fin nodes :=
  ⟨Z.nodeIndex key m p hp fit venue (gate e batch),
    (Z.nodeIndex_bound key m p hp fit venue (gate e batch)).trans_le budget⟩

theorem numbered_tree_gate {nodes : ℕ} (budget : (2*DescentNetworkSubstitution.portLoad Z.bank venue)/p≤nodes) :
    (Z.numberedTreeGate key m p hp fit s t q e batch budget).val=
      (before (Contact.cellKey ids code q.1.val q.2) e).card*m+batch.val :=
  installedTreeIndex Z.placement Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t q e batch

theorem reached_tree_range (localMul : ∀a,boundaryWidth raw q a=boundaryWidth raw q a/p*p) (slot : ℕ) (field : Fin 3) :
    atSlot (r:=Z.laneRecipe key m p hp fit venue) (Z.laneShape key m p hp fit venue) (gate e batch) slot field=
      atSlot (r:=(rawOp).recipe) (ofProgram (fun a=>boundaryWidth raw q a/p) localMul hp rawOp) (e,batch) slot field :=
  installedTreeRange Z.placement Z.graph Z.positive Z.pay Z.circuit key d m p hp fit s t q e batch
    (Z.laneWidth_eq m p fit venue) localMul slot field

end
end Hierarchy.DescentSixParty.ResetInput

end OAI

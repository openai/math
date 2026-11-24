import OAI.Computability.VPVNP.PairRefreshTraversalLabels
import OAI.Computability.VPVNP.RefreshProcedureWitness
import OAI.Computability.VPVNP.PairSimulationPrivateLabels

/-!
# Evaluation of the local refresh action

The old physical node is the unique preimage of the promoted site. The product
of the scalar labels emitted by the native local visit is the selected dyadic
refresh kernel over every specialization of the common parameter equations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open Compression Compression.Refresh Compression.DegreeRefresh NetworkKernel
open PairSimulation MotifConversion RefreshMapOperands

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {hist g : ℕ} (order : B.Entry ≃ Fin hist) (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent))

local notation "port" => bitWordFinEquiv S.portExponent
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "splitIso" => relaneIso X.slots (splitBitWord S.portExponent g) X.width

/-- The numerical refresh placement is the lane split followed by port promotion. -/
noncomputable def place : X.network.Site ≃ (X.Base × Fin (2 ^ S.portExponent)) × BitWord g :=
  ((Equiv.refl X.Base).prodCongr (splitBitWord S.portExponent g).toEquiv).trans
    (refreshPositions (bitWordFinEquiv _))

theorem old_place : promotedSites v = place X (oldSite X v) := by
  change ((v.1.1, v.2), v.1.2) = refreshPositions port (v.1.1,
    splitBitWord S.portExponent g ((splitBitWord S.portExponent g).symm ((port).symm v.2, v.1.2)))
  rw [AddEquiv.apply_symm_apply, refreshPositions_apply, Equiv.apply_symm_apply]

variable (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh
    S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))

/-- Fill the kernel's placed argument with the sole old half-wire assignment. -/
def placedHalf : Placed (place X) X.network.Half (promotedSites v) :=
  fun u hu => (show oldSite X v = u from (place X).injective ((old_place X v).symm.trans hu)) ▸ old

theorem placedHalf_unique (before : Placed (place X) X.network.Half (promotedSites v)) :
    placedHalf X v (before (oldSite X v) (old_place X v)) = before := by
  funext u hu
  obtain rfl := (place X).injective ((old_place X v).symm.trans hu)
  rfl

variable (before : Placed (place X) X.network.Half (promotedSites v))
local notation "older" => before (oldSite X v) (old_place X v)

/-- Pull the placed old half-wire assignment through the lane-splitting isomorphism for use by
the refresh kernel. -/
noncomputable def splitPlaced :
    Placed (refreshPositions port) (actualWireGraph (splitSlots X) (splitWidths X)).Half
      (promotedSites v) :=
  fun u hu => (splitIso).pullHalf u (before ((splitIso).site u) (by
    change promotedSites v = refreshPositions port (u.1,
      splitBitWord S.portExponent g ((splitBitWord S.portExponent g).symm u.2))
    rwa [AddEquiv.apply_symm_apply]))

theorem splitPlaced_child :
    splitPlaced X v before (originalSites port v)
      (by simp [promotedSites, originalSites, refreshPositions]) =
      (splitIso).pullHalf (originalSites port v) older := rfl

local notation "indices" => refreshEntryIndices (splitSlots X) port (splitWidths X)
  S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice v (splitPlaced X v before) new

/-- Decode the finite histogram labels back into the common parameter alphabet. -/
def evalLabels {K : Type*} [CommMonoidWithZero K] (f : B.Entry → K)
    (labels : Option (List (Fin hist))) : K :=
  labels.elim 0 fun ls => (ls.map (f ∘ order.symm)).prod

theorem eval_emitted_indices {K : Type*} [CommMonoidWithZero K] (f : B.Entry → K) :
    evalLabels B order f (emitted B order X choice v older new) =
      evalEntry (f ∘ Sum.inr) indices := by
  rw [emitted_eq_indices B order X choice v older new (splitPlaced X v before)
    (splitPlaced_child X v before)]
  cases indices with
  | none => rfl
  | some labels =>
    simp only [Option.map_some, evalLabels, Option.elim_some, evalEntry,
      List.map_ofFn, List.prod_ofFn, Function.comp_apply, Equiv.symm_apply_apply]

variable {K : Type*} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)

local notation "hsol" => And.right (Iff.mp (B.solution_iff f) hf)
local notation "step" => expanderRefreshStep (splitSlots X) port (splitWidths X) S.graph
  (Nat.two_pow_pos _) hc B.refresh (f ∘ Sum.inr) hsol S.port_order hd
local notation "pass" => dyadicRefreshPass X S.graph (Nat.two_pow_pos _) hc B.refresh
  S.port_order hd (f ∘ Sum.inr) hsol

set_option maxHeartbeats 1500000 in
-- Reduce the reindexed kernel on the singleton placed half.
/-- The physical action evaluates to the exact coefficient of the scheduled dyadic
refresh. Its value is zero on either failed local test. -/
theorem eval_emitted_kernel :
    evalLabels B order f (emitted B order X choice v older new) =
      (((pass).step.term choice).kernel (promotedSites v) before new) := by
  rw [eval_emitted_indices]
  have raw := refreshEntryIndices_spec (splitSlots X) port (splitWidths X) S.graph
    (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice v (splitPlaced X v before)
    new (f ∘ Sum.inr) hsol
  apply raw.symm.trans
  change ((step).term choice).kernel (promotedSites v) (splitPlaced X v before) new =
    ((((step).term choice).reindex splitIso (Network.Iso.refl _)).kernel (promotedSites v)
      before new)
  unfold Term.reindex
  erw [Equiv.piCongrLeft_refl]
  rfl

/-- The same identity directly on the independently stored child and parent halves. -/
theorem eval_emitted_singleton :
    evalLabels B order f (emitted B order X choice v old new) =
      (((pass).step.term choice).kernel (promotedSites v) (placedHalf X v old) new) :=
  eval_emitted_kernel B order X choice v new (placedHalf X v old) f hf

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI

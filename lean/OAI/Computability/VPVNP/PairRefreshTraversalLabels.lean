import OAI.Computability.VPVNP.PairRefreshTraversalMapBody

/-!
# Labels of the resident refresh role

The two stored node arguments select the same diagonal tests and scalar list as the
dyadic refresh kernel. The physical parent may receive its old half through any
placement with the prescribed singleton child.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open Compression Compression.Refresh Compression.DegreeRefresh NetworkKernel PairSimulation
open MotifConversion MotifEntry MotifDemandPadding MotifSelector LocalHistory RefreshMapOperands

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  {hist g : ℕ} (order : B.Entry ≃ Fin hist) (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent))
  (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))

local notation "G" => splitSlots X
local notation "port" => bitWordFinEquiv (S.portExponent)
local notation "widths" => splitWidths X
local notation "t" => oldPortMatching G port
local notation "ws" => groupedWidths port widths
local notation "P" => S.graph.toSlotGraph
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "supply" =>
  blockSupplyWidths G port widths S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "oldArg" => oldHalf X v old
local notation "seg" => segments X v P S.port_order hd supply new
local notation "I" => entryInput B X choice v old new
local notation "splitIso" => relaneIso X.slots (splitBitWord S.portExponent g) X.width

set_option maxHeartbeats 1800000 in
-- Matching the two label formulas unfolds the complete dependent refresh entry.
/-- The addressable labels, including repetitions, are the exact common scalar
indices of the refresh kernel for these arguments. -/
theorem emitted_eq_indices
    (before : Placed (refreshPositions port) (actualWireGraph G widths).Half (promotedSites v))
    (child : before (originalSites port v)
      (by simp [promotedSites, originalSites, refreshPositions]) =
      (splitIso).pullHalf (originalSites port v) old) :
    emitted B order X choice v old new =
      ((refreshEntryIndices G port widths S.graph
        (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice
        v before new).map List.ofFn).map (List.map (fun e => order (.inr e))) := by
  classical
  let good := (oldArg).1 ((v.1, v.2), v.2) rfl = (seg).1 v.2 ∧
    (seg).2 v.2 = incomingHalf (R := ℤ) t ws v.1 v.2 v.2 oldArg
  have diag : portDiagonal t ws v.1 v.2 oldArg seg = (1 : ℤ) ↔ good := by
    unfold portDiagonal segmentTest
    dsimp only [good]
    split <;> split <;> rename_i h₁ h₂
    · exact ⟨fun _ => ⟨h₁, h₂⟩, fun _ => rfl⟩
    · exact ⟨by norm_num, fun h => (h₂ h.2).elim⟩
    · exact ⟨by norm_num, fun h => (h₁ h.1).elim⟩
    · exact ⟨by norm_num, fun h => (h₁ h.1).elim⟩
  unfold emitted refreshEntryIndices
  dsimp only
  rw [child]
  let ids := entry B.refresh (fun _ => zero_lt_one) (EntryInput.demand I) (EntryInput.payload I) v.2
    (EntryInput.demandBits I) (EntryInput.supplyBits I)
  change (if portDiagonal t ws v.1 v.2 oldArg seg = (1 : ℤ) then _ else none) =
    ((if good then ids else none).map List.ofFn).map (List.map (fun e => order (.inr e)))
  by_cases eqn : good
  · rw [ite_eq_left (diag.mpr eqn), ite_eq_left eqn]
    exact congrArg (Option.map (List.map (fun e => order (.inr e))))
      (runEntry_list B.refresh (fun _ => zero_lt_one) (EntryInput.demand I) (EntryInput.payload I)
        v.2 (EntryInput.demandBits I) (EntryInput.supplyBits I))
  · rw [ite_eq_right (mt diag.mp eqn), ite_eq_right eqn]
    rfl

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI

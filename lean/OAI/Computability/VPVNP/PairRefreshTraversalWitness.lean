import OAI.Computability.VPVNP.PairRefreshTraversalValue
import OAI.Computability.VPVNP.PairSelectedKernelReaders

/-!
# Witnesses and histogram exponents at the selected refresh node

An emitted list corresponds to one local witness, even when a selected scalar is
zero in the field. Each histogram bin records exactly the exponent of the matching
parameter in that witness.
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
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh
    S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
  (before : Placed (place X) X.network.Half (promotedSites v))
  {K : Type*} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)

local notation "port" => bitWordFinEquiv S.portExponent
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "hsol" => And.right (Iff.mp (B.solution_iff f) hf)
local notation "older" => before (oldSite X v) (old_place X v)
local notation "idx" => refreshEntryIndices (splitSlots X) port (splitWidths X)
  S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice v (splitPlaced X v before) new
local notation "W" => dyadicRefreshKernelWitness X S.graph (Nat.two_pow_pos _) hc B.refresh
  S.port_order hd (f ∘ Sum.inr) hsol choice (promotedSites v) before new

private theorem count_right {L M : Type} {u : ℕ}
    (ord : L ⊕ M ≃ Fin hist) (labels : Fin u → M) (a : L ⊕ M) :
    ((List.ofFn labels).map (fun e => ord (.inr e))).count (ord a) =
      Sum.elim (fun _ => 0) (entryMultiplicity labels) a := by
  classical
  have h := PrivateLabels.count_entry (fun i => (Sum.inr (labels i) : L ⊕ M)) ord a
  rw [List.map_ofFn] at h ⊢
  refine h.trans ?_
  cases a with
  | inl l => simp [entryMultiplicity]
  | inr l => simp [entryMultiplicity]

private theorem choices_of_indices {Label : Type} [Fintype Label] {u : ℕ}
    (scalar : Label → K) (indices : Option (Fin u → Label)) :
    Nonempty (entryWitness scalar indices).Choice ↔ indices.isSome = true := by
  cases indices with
  | none => exact ⟨fun ⟨c⟩ => c.elim, fun h => by cases h⟩
  | some _ => exact ⟨fun _ => rfl, fun _ => ⟨()⟩⟩

set_option maxHeartbeats 1600000 in
-- Identify the reindexed witness with its finite entry choice.
/-- The branch is admissible exactly when the native role emits a list. -/
theorem emitted_iff_witness :
    (emitted B order X choice v older new).isSome = true ↔ Nonempty (W).Choice := by
  rw [emitted_eq_indices B order X choice v older new (splitPlaced X v before)
    (splitPlaced_child X v before)]
  simp only [Option.isSome_map]
  exact (choices_of_indices (f ∘ Sum.inr) idx).symm

private theorem indexed_counts {L M : Type} [Fintype M] {u : ℕ}
    (ord : L ⊕ M ≃ Fin hist) (scalar : M → K) (ids : Option (Fin u → M))
    (w : (entryWitness scalar ids).Choice) (label : L ⊕ M) :
    ((ids.map List.ofFn |>.map (List.map (fun e => ord (.inr e)))).getD []).count (ord label) =
      Sum.elim (fun _ => 0) ((entryWitness scalar ids).exponents w) label := by
  cases ids with
  | none => exact w.elim
  | some labels => exact count_right ord labels label

set_option maxHeartbeats 1800000 in
-- Compare the reindexed exponent with the count in the selected label list.
/-- Histogram multiplicity of every global parameter equals the exponent of the
scheduled refresh witness, including the zero exponents on shrinking parameters. -/
theorem emitted_count (w : (W).Choice) (label : B.Entry) :
    ((emitted B order X choice v older new).getD []).count (order label) =
      (MonomialWitness.right f W).exponents w label := by
  rw [emitted_eq_indices B order X choice v older new (splitPlaced X v before)
    (splitPlaced_child X v before)]
  change (((idx).map List.ofFn |>.map (List.map (fun e => order (.inr e)))).getD []).count
    (order label) = Sum.elim (fun _ => 0) ((entryWitness (f ∘ Sum.inr) idx).exponents w) label
  exact indexed_counts order (f ∘ Sum.inr) idx w label

local notation "reader" => LocalHistory.originReader B f hf
  (VPVNP.CompressorRecords.PassOrigin.refresh X) choice

/-- The scheduled term reader has a kernel witness exactly on the accepted
branch, for every physical specialization of the common equations. -/
theorem origin_emitted_iff :
    (emitted B order X choice v older new).isSome = true ↔
      Nonempty ((reader).witness (promotedSites v) before new).Choice :=
  emitted_iff_witness B order X choice v new before f hf

private theorem subsingleton_indices {Label : Type} [Fintype Label] {u : ℕ}
    (scalar : Label → K) (indices : Option (Fin u → Label)) :
    Subsingleton (entryWitness scalar indices).Choice := by
  cases indices with
  | none => exact inferInstanceAs (Subsingleton Empty)
  | some _ => exact inferInstanceAs (Subsingleton Unit)

/-- An accepted port has exactly one local kernel witness even after a parameter
specialization sending its monomial to zero. -/
theorem origin_witness_unique
    (accepted : (emitted B order X choice v older new).isSome = true) :
    ∃! _w : ((reader).witness (promotedSites v) before new).Choice, True := by
  obtain ⟨w⟩ := (origin_emitted_iff B order X choice v new before f hf).mp accepted
  have subs : Subsingleton ((reader).witness (promotedSites v) before new).Choice :=
    subsingleton_indices (f ∘ Sum.inr) idx
  exact ⟨w, trivial, fun y _ => subs.elim y w⟩

/-- Per-bin effect in the exact exponent ABI of the selected term reader. -/
theorem origin_emitted_count (w : ((reader).witness (promotedSites v) before new).Choice)
    (label : B.Entry) :
    ((emitted B order X choice v older new).getD []).count (order label) =
      ((reader).witness (promotedSites v) before new).exponents w label :=
  emitted_count B order X choice v new before f hf w label

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI

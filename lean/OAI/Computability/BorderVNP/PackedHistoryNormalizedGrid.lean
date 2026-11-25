import OAI.Computability.BorderVNP.PackedHistoryNormalizedGridRoutes
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGridShape
import OAI.Computability.BorderVNP.PackedHistoryNormalizedTransport

/-! # The assigned grouped grid at the base of the normalized site history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Packing Packing.PhysicalEpochs Packing.DeckGrid
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction Shortening.PreparedBins
open Shortening.PublicCapacity Shortening.Adaptive
open VPVNP.VerifierNetwork (Frame)
open scoped Classical
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {R r t pins link inner n : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge) (d : ℕ)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (copies : ℕ) {w : ℕ}

local notation "axes" => Fintype.card (Cube D)
local notation "N" => seedBundle G axes d order position copies
local notation "B" => SelectedSchedule.boundary S (d+1)
local notation "tileWidth" => GridHosts.inputBlockWidth r n axes d
local notation "O" => Pins S (d+1) B w

/-- The assigned bottom pack carries the exact public grid routes, tile and direction
numbers, arbitrary private field tables, and the words computed by the initializer. -/
noncomputable def seedState (table : (N).Tables K) (words : O 0 → Bool) :
    State S (d+1) (Fin (GridHosts.tileCount axes d)) (fun _ => copies*tileWidth) B O 0 :=
  ⟨⟨N,table⟩,seedRoutes S G d order position copies table,
    returnedRows (p := Pack.mk N table) (gridShape_zero S d) (groupedGridRows G axes d order position copies),
    fun _ => (1 : Fin axes → Deck (d+2)),words⟩

private theorem rowNumbers {D : ℕ} {P : Type} {K : Type*} {bits : P → ℕ} (p : Pack D P bits K)
    {s s' : Shape} (hs : s' = s) (rows : Rows s p.layout) :
    (∀ v, ((returnedRows (p := p) hs rows).site v).val = (rows.site v).val) ∧
    (∀ a, ((returnedRows (p := p) hs rows).edge a).val = (rows.edge a).val) := by
  subst s'; exact ⟨fun _ => rfl,fun _ => rfl⟩

/-- The row of an exterior block is its original tile ordinal. The cable row is the
row-major pair of its source tile ordinal and its physical Cayley direction. -/
theorem seedState_rows (table : (N).Tables K) (words : O 0 → Bool) :
    let a := seedState S G d order position copies table words
    (∀ i, (a.rows.site (a.pack.layout.attach i)).val = i.val) ∧
    (∀ z : (N).Edge, (a.rows.edge z).val =
      (finProdFinEquiv (order.symm z.1,Fintype.equivFin (Direction axes) z.2)).val) := by
  intro a
  have ids := rowNumbers (Pack.mk N table) (gridShape_zero S d) (groupedGridRows G axes d order position copies)
  refine ⟨fun i => (ids.1 (order i)).trans ?_,ids.2⟩
  exact congrArg Fin.val (order.symm_apply_apply i)

set_option maxHeartbeats 1200000 in
/-- A single two-gate initializer supplies every physical row on all private tables of
the grouped seed. Its expanded budget is the measured box, cable, and external cost on
each original tile, with the supplied retained descriptor and payload fields. -/
theorem exists_seed_frame (σ : Type) [Fintype σ] (fit : GridHosts.tileCount axes d ≤ 2^w)
    (small : copies * seedChannelWidth n r axes d < 2^w) :
    ∃ base : Frame σ (O 0), base.size ≤ 2 ∧
    ∀ (table : (N).Tables K) (x : σ → Bool) (budget : ℕ → ℕ) (prior payload : (N).Site → ℕ),
      (∀ v, boxCost true (prior v) (payload v) +
        2*Fintype.card (Direction axes)*recordCost true (copies*seedChannelWidth n r axes d) +
        recordCost true (copies*tileWidth) ≤ budget 0) →
      Good budget 0 (seedState S G d order position copies table (base.eval x)) := by
  let zero : (N).Tables K := fun _ _ _ => 0
  let p := Pack.mk N zero
  let row := returnedRows (p := p) (gridShape_zero S d) (groupedGridRows G axes d order position copies)
  let route := seedRoutes S G d order position copies zero
  have fit' : (B 0).sites ≤ 2^w := by rw [gridShape_zero]; exact fit
  obtain ⟨base,cost,ready⟩ := RouteRows.ready_constant_frames (factorEnum D) p route row (fun _ => (1 : Fin axes → Deck (d+2))) σ fit' (fun _ => small)
  refine ⟨base,cost,?_⟩
  intro table x budget prior payload within
  constructor
  · obtain ⟨names,origins,present,active,hole,move⟩ := ready x
    exact ⟨names,origins,present,active,hole,move⟩
  · refine ⟨⟨prior,payload⟩,?_⟩
    intro tile
    let orderCube := GridShape.coordinate (d := d+1) (factorEnum D).symm
    let v := orderCube.symm tile
    have same : (fun y : (N).Site => reduceMove (d+1) ((seedRoutes S G d order position copies table).origin y) = tile)
        = (· = v) := by
      funext y
      rw [seed_origin]
      exact propext orderCube.eq_symm_apply.symm
    change @localRecords D _ (portFintype (k := fan S) (P := Fin (GridHosts.tileCount axes d)) (b := 0)) _
      N true prior payload (fun y => reduceMove (d+1) ((seedRoutes S G d order position copies table).origin y) = tile) ≤ budget 0
    rw [same,show portFintype (k := fan S) (P := Fin (GridHosts.tileCount axes d)) (b := 0) =
        Fin.fintype (GridHosts.tileCount axes d) from Subsingleton.elim _ _]
    exact (seed_localRecords G axes d order position copies true prior payload v).trans_le (within v)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI

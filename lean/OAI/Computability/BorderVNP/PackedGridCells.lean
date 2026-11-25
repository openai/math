import OAI.Computability.BorderVNP.PackedGrid
import OAI.Computability.BorderVNP.PackedSubdivision
import OAI.Computability.BorderVNP.ShortenEpochLocalRecords

/-! # Public Cayley cells for the private routes of Proposition 7.2

A cell and a generator index determine each channel and its two endpoints, whether or
not a private route uses the channel. Packing uses the private hop directions and their
congestion bound. The local record count charges both ends separately, including loops.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open BorderVNP.Shortening Finset
open scoped Classical
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {G J : Type} [Group G] [Fintype G] [Fintype J]
variable (cell : N.Site → G) (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable (step : J → G) (H : ℕ)

/-- The directed cable numbered `(g,j)` runs from `g` to `g * step j`. -/
noncomputable abbrev cayleyGrid : Network D P bits :=
  (N.cellNetwork cell position).uniformGrid (fun q : G × J => q.1) (fun q => q.1 * step q.2) H

/-- Load counted at a cell's source ends on the distinct-cell wires. -/
noncomputable def crossingLoad (g : G) : ℕ :=
  ∑ e : N.CrossingEdge cell, if cell (N.src e.val) = g then N.width e.val else 0

/-- Choose a neighbor label privately for each crossing hop. A bound on the outgoing
width at a cell bounds the load of every one of its directed cables. -/
noncomputable def cayleyPacking
    (neighbor : ∀ e : N.CrossingEdge cell, ∃ j, cell (N.src e.val) * step j = cell (N.dst e.val))
    (congestion : ∀ g, N.crossingLoad cell g ≤ H) :
    (N.cellNetwork cell position).ChannelPacking (fun q : G × J => q.1)
      (fun q => q.1 * step q.2) H := by
  let ch (e : N.CrossingEdge cell) : G × J := (cell (N.src e.val), (neighbor e).choose)
  refine ⟨ch, fun _ => rfl, fun e => (neighbor e).choose_spec, fun q => ?_⟩
  have hsum : (∑ e : {e : N.CrossingEdge cell // ch e = q}, N.width e.val.val) =
      ∑ e : N.CrossingEdge cell, if ch e = q then N.width e.val else 0 := by
    rw [← sum_filter, sum_subtype (p := fun e => ch e = q) _ (fun _ => by simp)]
  apply le_trans (b := ∑ e : {e : N.CrossingEdge cell // ch e = q}, N.width e.val.val)
  · exact (sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun _ _ => rfl).le
  rw [hsum]
  apply le_trans _ (congestion q.1)
  apply sum_le_sum
  intro e _
  by_cases he : ch e = q
  · simp [he, show cell (N.src e.val) = q.1 from congrArg Prod.fst he]
  · simp [he]

/-- The cell boxes and all public neighbor cables together compute the original fine
network on the same external input. -/
theorem value_cayleyGrid {R : Type*} [CommSemiring R] (table : N.Tables R) (x : Ports bits)
    (neighbor : ∀ e : N.CrossingEdge cell, ∃ j, cell (N.src e.val) * step j = cell (N.dst e.val))
    (congestion : ∀ g, N.crossingLoad cell g ≤ H) :
    (N.cayleyGrid cell position step H).value
      ((N.cayleyPacking cell position step H neighbor congestion).tables
        (N.cellTables cell position table)) x = N.value table x :=
  ((N.cayleyPacking cell position step H neighbor congestion).value_uniformGrid _ x).trans
    (N.value_cellNetwork cell position table x)

/-- Subdivide the original routes, retain same-cell hops in their boxes, and pack the
remaining wires into the public grid. The output tensor is unchanged for every input. -/
theorem exists_grid_of_routes {R : Type*} [CommSemiring R] (table : N.Tables R)
    (routes : N.WireRoutes) (cells : (N.subdivide routes).Site → G)
    (neighbor : ∀ e : (N.subdivide routes).CrossingEdge cells,
      ∃ j, cells ((N.subdivide routes).src e.val) * step j = cells ((N.subdivide routes).dst e.val))
    (congestion : ∀ g, (N.subdivide routes).crossingLoad cells g ≤ H) :
    ∃ table' : ((N.subdivide routes).cayleyGrid cells position step H).Tables R,
      ∀ x, ((N.subdivide routes).cayleyGrid cells position step H).value table' x = N.value table x :=
  ⟨_, fun x => ((N.subdivide routes).value_cayleyGrid cells position step H
    (N.subdivideTables routes table) x neighbor congestion).trans (N.value_subdivide routes table x)⟩

/-- Exact descriptor count at any public grid cell. In expanded mode, a cable record
also charges all its bits. Each generator has one initial and one final end at the cell. -/
theorem cayleyGrid_records [Fintype P] (expanded : Bool) (prior payload : G → ℕ) (g : G) :
    localRecords (N.cayleyGrid cell position step H) expanded prior payload (· = g) =
      boxCost expanded (prior g) (payload g) + 2 * Fintype.card J * recordCost expanded H +
        testedWidth (fun i => recordCost expanded (bits i)) (fun i => cell (N.attach i) = g) := by
  let w := recordCost expanded H
  have src : (∑ q : G × J, if q.1 = g then w else 0) = Fintype.card J * w := by
    rw [Fintype.sum_prod_type_right]
    simp
  have dst : (∑ q : G × J, if q.1 * step q.2 = g then w else 0) = Fintype.card J * w := by
    rw [Fintype.sum_prod_type_right]
    have leg (j : J) : (∑ s : G, if s * step j = g then w else 0) = w := by
      calc
        _ = ∑ s : G, if s = g then w else 0 :=
          Equiv.sum_comp (Equiv.mulRight (step j)) (fun s => if s = g then w else 0)
        _ = _ := by simp
    simp [leg]
  unfold localRecords
  change (∑ i : G, if i = g then boxCost expanded (prior i) (payload i) else 0) +
    (∑ q : G × J, if q.1 = g then w else 0) + (∑ q : G × J, if q.1 * step q.2 = g then w else 0) +
    _ = _
  rw [src, dst]
  simp only [sum_ite_eq', mem_univ, ite_true]
  dsimp only [w]
  ring

end Crossing.Network

end BorderVNP
end Computability
end OAI

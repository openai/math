import OAI.Computability.BorderVNP.PackedGridWalks
import OAI.Computability.BorderVNP.PackedGridDeck
import OAI.Computability.BorderVNP.PackedGridRepeat

/-! # Routing a degree-three bit network into a fixed public grid

The integral width bound depends on the endpoint multiplicity, the host diameter
and its site count. The same intermediate choices control the private equality
descriptions and the congestion of all public cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open Crossing Shortening Finset
open scoped Classical
variable {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)
variable {G J : Type} [Group G] [Fintype G] (place : N.Site → G)
variable (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable (step : J → G) (invStep : ∀ j, ∃ k, step k = (step j)⁻¹) (k h : ℕ)

/-- A public integer congestion bound shared by all allowed directed neighbor cables. -/
def cableWidth (G : Type) [Fintype G] (k h : ℕ) : ℕ :=
  8*k*(h+1) + Nat.clog 2 (Fintype.card G)

/-- The host and integer parameters determine the cap using only binary lengths. -/
theorem real_bound_le_cableWidth (G : Type) [Fintype G] [Nonempty G] (k h : ℕ) :
    8*(k:ℝ)*(h+1) + Real.log (Fintype.card G) ≤ cableWidth G k h := by
  simp only [cableWidth,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  apply add_le_add_right
  let m := Nat.clog 2 (Fintype.card G)
  have hh : (Fintype.card G : ℝ) ≤ (2:ℝ)^m := by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (Fintype.card G)
  have ht : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ Real.log ((2:ℝ)^m) := Real.log_le_log (Nat.cast_pos.mpr Fintype.card_pos) hh
    _ = m * Real.log 2 := Real.log_pow ..
    _ ≤ m := by simpa using mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg m)

/-- The actual ordered walks, with one common public upper bound on all visit totals. -/
structure Routed where
  /-- Sequence of adjacent host sites for every fine wire. -/
  walk : ∀ e : N.Edge, (CayleyPaths.graph step invStep).Walk (place (N.src e)) (place (N.dst e))
  /-- All inserted boxes at a tile, counting each visit separately. -/
  visits : ∀ g, (∑ e, (walk e).support.count g) ≤ cableWidth G k h

/-- Bounded endpoint multiplicity and the host word diameter suffice to choose all the
private routes simultaneously. The choice requires no table contents or scalar values. -/
theorem exists_routed
    (hs : ∀ g, (univ.filter fun e => place (N.src e) = g).card ≤ k)
    (hd : ∀ g, (univ.filter fun e => place (N.dst e) = g).card ≤ k)
    (short : ∀ u : G, ∃ w : List J, w.length ≤ h ∧ (w.map step).prod = u) :
    Nonempty (Routed N place step invStep k h) := by
  obtain ⟨walk,hw⟩ := CayleyPaths.exists_walks step invStep (fun e => place (N.src e))
    (fun e => place (N.dst e)) k h hs hd short
  refine ⟨walk,fun g => ?_⟩
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_sum]
  exact (hw g).trans (real_bound_le_cableWidth G k h)

variable {N place step invStep k h} (r : Routed N place step invStep k h)

/-- The physical subdivision used for the exact equality factors in this placement. -/
abbrev wireRoutes := WalkLayout.routes N _ place r.walk position

/-- The private site-to-cell map on all original and inserted equality boxes. -/
abbrev cell := WalkLayout.cells N _ place r.walk position

/-- For a bit network the sum of all crossing widths leaving each cell is bounded by
its total visit count. -/
theorem outgoing_le (unit : ∀ e, N.width e ≤ 1) (g : G) :
    (N.subdivide (wireRoutes position r)).crossingLoad (cell position r) g ≤ cableWidth G k h := by
  apply (WalkLayout.crossingLoad_le N _ place r.walk position g).trans
  apply le_trans _ (r.visits g)
  exact sum_le_sum fun e _ => (Nat.mul_le_mul_right _ (unit e)).trans_eq (one_mul _)

/-- Bounds on private box descriptions can charge each retained original item and at
most five extra records/bit occurrences per route visit (one site and its two one-bit ends). -/
theorem private_records_le [Fintype P] (unit : ∀ e, N.width e ≤ 1)
    (expanded : Bool) (prior payload : N.Site → ℕ) (g : G) :
    localRecords (N.subdivide (wireRoutes position r)) expanded
      (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun _ => 0)) (fun v => cell position r v = g) ≤
    localRecords N expanded prior payload (fun v => place v = g) + 5 * cableWidth G k h := by
  rw [WalkLayout.fine_records]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ e, 5 * (r.walk e).support.count g := by
      apply sum_le_sum
      intro e _
      apply Nat.mul_le_mul_right
      have hu := unit e
      cases expanded with
      | false => simp [recordCost]
      | true => simp [recordCost]; omega
    _ ≤ _ := by rw [← mul_sum]; exact Nat.mul_le_mul_left _ (r.visits g)

variable [Fintype J]
include r

/-- The fine routed network is realized on exactly the public equal-width grid. All
private choices occur inside its site tables. -/
theorem exists_tables {R : Type*} [CommSemiring R] (unit : ∀ e, N.width e ≤ 1) (table : N.Tables R) :
    ∃ t : (N.cayleyGrid place position step (cableWidth G k h)).Tables R,
      ∀ x, (N.cayleyGrid place position step (cableWidth G k h)).value t x = N.value table x := by
  have near (e : (N.subdivide (wireRoutes position r)).CrossingEdge (cell position r)) :=
    (WalkLayout.adjacent N (CayleyPaths.graph step invStep) place r.walk position e).2
  exact N.exists_grid_of_routes position step (cableWidth G k h) table (wireRoutes position r)
    (cell position r) near (outgoing_le position r unit)

/-- The bottom pack on the fixed grid computes the original `b` independent batches
on the same numbered external slots. Only the internal cable widths grow by `b`. -/
theorem exists_bottom_bundle {R : Type*} [CommSemiring R] (unit : ∀ e, N.width e ≤ 1)
    (table : N.Tables R) (b : ℕ) :
    ∃ t : (N.cayleyGrid place position step (cableWidth G k h)).Tables R,
      let M := N.cayleyGrid place position step (cableWidth G k h)
      (Pack.mk (M.repeatGrid b) (M.repeatTables b t)).tensor =
        (parallelPacks (fun _ : Fin b => (⟨N,table⟩ : ValuedPack R D bits))).tensor := by
  obtain ⟨t,ht⟩ := exists_tables position r unit table
  refine ⟨t,?_⟩
  funext x
  exact ((N.cayleyGrid place position step (cableWidth G k h)).value_repeatGrid b t x).trans
    ((prod_congr rfl fun i _ => ht (fun p => x (i,p))).trans
      (Network.parallel_value (fun _ : Fin b => N) (fun _ => table) x).symm)

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI

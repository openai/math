import OAI.Computability.BorderVNP.FinitePrewireNetwork
import OAI.Computability.BorderVNP.DiagonalInitialGridRouted
import OAI.Computability.BorderVNP.PackedGridSlots
import OAI.Computability.BorderVNP.FiniteTeamContraction
import OAI.Computability.BorderVNP.FiniteLocalCellScan

/-! # Public deck-grid placement of an arbitrary proposed finite-field batch

All interior assignments are summed by the fine network before its routes
are chosen. Its public leaves follow the live field ordering and the full
processor-word address stride. Each padded channel's table is the actual
local aggregation of the routed, subdivided input factors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FinitePrewire

open Crossing ParseBatch Prewire Packing Packing.GridPlacement Cover TeamContraction
open scoped BigOperators Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    {G : Type} [Group G] [Fintype G] {J : Type} [Fintype J]
    {place : N.Site → G} {step : J → G} {invStep : ∀ j, ∃ j', step j' = (step j)⁻¹} {load h : ℕ}
    (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (route : Routed N place step invStep load h) (unit : ∀ e, N.width e ≤ 1)

/-- Concrete polynomial or field table formed by local equality subdivision,
private cell contraction and padded packing on the certified ordered routes. -/
noncomputable def routedTables {A : Type*} [CommSemiring A] (table : N.Tables A) :
    (N.cayleyGrid place position step (cableWidth G load h)).Tables A :=
  (routedPacking position route unit).tables ((N.subdivide (wireRoutes position route)).cellTables
    (GridPlacement.cell position route) position (N.subdivideTables (wireRoutes position route) table))

omit [Fintype P] in
/-- The concrete routed grid computes the fine tensor on every retained port assignment. -/
theorem routed_value {A : Type*} [CommSemiring A] (table : N.Tables A) (x : Ports bits) :
    (N.cayleyGrid place position step (cableWidth G load h)).value (routedTables position route unit table) x =
      N.value table x := by
  exact ((routedPacking position route unit).value_uniformGrid _ x).trans
    (((N.subdivide (wireRoutes position route)).value_cellNetwork (GridPlacement.cell position route) position
      (N.subdivideTables (wireRoutes position route) table) x).trans (N.value_subdivide _ _ x))

/-- Each public padded grid entry reads its private boundary slices, then
runs the finite-field scan of the *local* routed component. The assignment
type below contains only the cables wholly inside the named cell. -/
theorem routedTables_scan {F : Type*} [Field F] [Fintype F] (table : N.Tables F) :
    let B := N.subdivide (wireRoutes position route)
    let cell := GridPlacement.cell position route
    let T := N.subdivideTables (wireRoutes position route) table
    routedTables position route unit table = (routedPacking position route unit).tables (fun c a x =>
      let L := FiniteLocalCell.network B cell c
      let sites := FiniteLocalCell.siteList B cell c
      let w := Nat.clog 2 (sites.length+1)
      ∑ z : L.Assignment, ∑ report : Fin (Fintype.card F) → Fin w → Bool,
        FieldDirectory.scan L sites (FiniteLocalCell.tables B cell c T) w z
          (FiniteLocalCell.ports B cell c a x) report) := by
  intro B cell T
  apply congrArg (routedPacking position route unit).tables
  funext c a x
  exact (FiniteLocalCell.sum_scan_cellTables B cell c position T a x).symm

open private degree_eq from OAI.Computability.BorderVNP.PackedGridLanes

private theorem internal_degree_of_trivalent {S : Type} [Fintype S]
    (M : Network D S (fun _ => 1)) (hm : M.Trivalent) (v : M.Site) :
    (Finset.univ.filter fun e => M.src e = v).card +
      (Finset.univ.filter fun e => M.dst e = v).card ≤ 3 := by
  apply le_trans _ (hm.2 v)
  rw [degree_eq M v]
  exact Nat.le_add_right _ _

section Actual
variable {R r t d link inner n : ℕ} {Edge : Type} [Fintype Edge]
    (T : Wiring R r t d link inner n Edge)
    (B : Network D (Fin r × Fin n) (fun _ => 1))
    (q depth : ℕ)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (pos : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The visible fields use their processor-major addresses in the full r*n
leaf capacity; the private tensor realization has at most the proposed
volume plus the linear sewing overhead. -/
noncomputable def fieldGrid (volume : ℕ) :
    Network D (Fin r × Fin (publicWidth T)) (fun _ => 1) :=
  publicGridSlots pos (DeckGrid.step q (depth+2)) finProdFinEquiv order (fun _ => 1)
    (r*n) (Nat.mul_le_mul_left r ((Nat.le_add_right (publicWidth T) inner).trans T.fits))
    (volume + 15*(r*n)) (q*(1+3*depth^3))

/-- The routed physical tables are chosen before all visible field values
and recover the interior-summed tensor on every possible public assignment. -/
theorem field_grid_queries {A : Type*} [CommSemiring A]
    (volume : ℕ) (hV : B.bitVolume ≤ volume) (tri : B.Trivalent)
    (hedge : Fintype.card Edge ≤ r*inner) (table : B.Tables A) :
    ∃ gridTable : (fieldGrid T q depth order pos volume).Tables A,
      ∀ y : (Fin r × Fin (publicWidth T)) → Bool,
        (fieldGrid T q depth order pos volume).value gridTable (fun p _ => y p) =
          ∑ int : Edge → Bool, B.value table
            (fun p _ => readInput (Function.uncurry (source T)) y int p) := by
  let f := Function.uncurry (source T)
  let M := wired f B
  have hm : M.Trivalent := wired_trivalent f B tri
  have hi := wired_attach_injective f B
  have hs : Fintype.card M.Site ≤ volume + 15*(r*n) := by
    have hv := wired_volume f B (card_public_private_le T hedge)
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin] at hv
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (hv.trans (Nat.add_le_add_right hV _)))
  have fit := Nat.mul_le_mul_left r ((Nat.le_add_right (publicWidth T) inner).trans T.fits)
  obtain ⟨rt⟩ := routed_public_slots (DeckGrid.step q (depth+2)) finProdFinEquiv order M hi (r*n) fit
    (DeckGrid.inverse_letter q (depth+2)) hs (internal_degree_of_trivalent M hm) (DeckGrid.short_words q depth)
  unfold fieldGrid
  rw [← grid_eq_public_slots pos (DeckGrid.step q (depth+2)) finProdFinEquiv order M hi (r*n) fit]
  let unit : ∀ e, M.width e ≤ 1 := fun e => (hm.1 e).le
  refine ⟨routedTables pos rt unit (wiredTables f B table),?_⟩
  intro y
  exact (routed_value pos rt unit _ (fun p _ => y p)).trans (wired_value f B table y)

/-- The section's proposed arbitrary trivalent finite-field tensor is first
internally wired, then placed on the correct common grid. Every team reads
the same private tables, with its literal, exterior and pin values at the
actual public positions. -/
theorem field_grid_value {F : Type*} [Field F] [Fintype F]
    (volume : ℕ) (hV : B.bitVolume ≤ volume) (tri : B.Trivalent)
    (hedge : Fintype.card Edge ≤ r*inner) (table : B.Tables F)
    (computes : ∀ x, B.value table x = FiniteDiagonal.tensorPower F n r x) :
    ∃ gridTable : (fieldGrid T q depth order pos volume).Tables F,
      ∀ (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (team : Fin (R+1)),
      (fieldGrid T q depth order pos volume).value gridTable (fun p _ => publicBits T team pin ext p) =
        FieldTeam.fieldValue T F pin ext team := by
  obtain ⟨gridTable, hv⟩ := field_grid_queries T B q depth order pos volume hV tri hedge table
  refine ⟨gridTable,?_⟩
  intro pin ext team
  rw [hv]
  unfold FieldTeam.fieldValue
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro int _
  rw [computes, FiniteDiagonal.tensorPower]
  apply Finset.prod_congr (Finset.ext fun _ => by simp)
  intro j _
  exact congrArg (FPath.U F) (funext (source_read T team pin ext int j))

end Actual
end FinitePrewire

end BorderVNP
end Computability
end OAI

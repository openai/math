import OAI.Computability.BorderVNP.ShortenPublicSubdivisionRows
import OAI.Computability.BorderVNP.PackedGridBatch
import OAI.Computability.BorderVNP.PackedGridRepeat

/-!
# Bottom grid rows and the actual site moves at the start of an epoch

The repeated public grid keeps one site per product tile and one cable per
directed neighbor per tile. Repetition multiplies the cable width, without
adding any cable identifiers. For every nonlocal cable its public direction
gives an explicit allowed integral move with the recorded endpoints.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicCapacity

open Cover Epoch Crossing Packing DeckGrid GridPlacement
open scoped Classical

variable {q D z leaves copies s hops : ℕ} {P : Type} {bits : P → ℕ}

/-- The actual directed-neighbor public rectangle. -/
def gridShape (tiles directions : ℕ) : Shape := ⟨tiles,tiles*directions⟩

/-- The repeated bottom bundle has a fixed number of public rows per tile. -/
theorem grid_volume {tiles : ℕ} (ht : 1 ≤ tiles) (directions : ℕ) :
    (gridShape tiles directions).volume tiles ≤ (directions+3)*tiles := by
  simp only [gridShape,Shape.volume]
  nlinarith

variable (position : (Fin q → Deck (z+1)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable (input : P ≃ Fin leaves) (order : Fin (Fintype.card (Fin q → Deck (z+1))) ≃ (Fin q → Deck (z+1)))

/-- The public grid used for the repeated polynomial batch, with its literal
neighbor channels and per-channel binary widths. -/
noncomputable abbrev grid :=
  (GridPlacement.publicGrid position (DeckGrid.step q (z+1)) input order bits s hops).repeatGrid copies

/-- The physical bottom rows are identified by the given tile order, followed
by the public direction number within each tile. -/
noncomputable def gridRows : Rows (gridShape (Fintype.card (Fin q → Deck (z+1))) (Fintype.card (Direction q)))
    (grid position input order (bits := bits) (s := s) (hops := hops) (copies := copies)) where
  site := order.symm.toEmbedding
  edge := ((Equiv.prodCongr order.symm (Fintype.equivFin (Direction q))).trans finProdFinEquiv).toEmbedding

/-- The actual batch compiler uses the same stable rows for all copy counts. -/
noncomputable def batchGridRows {D q depth m r : ℕ} (copies : ℕ)
    (order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2)))
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) :
    Rows (gridShape (Fintype.card (Fin q → Deck (depth+2))) (Fintype.card (Direction q)))
      ((DeckGrid.batchGrid q depth m r order position).repeatGrid copies) :=
  gridRows position finProdFinEquiv order

variable {I : Type} [Fintype I] (enum : Fin q ≃ I)

/-- The integral lift of a public directed neighbor, in the physical factor ordering. -/
noncomputable def liftDirection (a : Direction q) : I → gamma 1 :=
  fun i => if enum.symm i = a.1 then ⟨a.2.val,routingGenerators_mem _ a.2.property⟩ else 1

omit [Fintype I] in
/-- Each integral letter reduces to its actual deck-grid channel. -/
theorem liftDirection_reduce (a : Direction q) (d : ℕ) (i : I) :
    (liftDirection enum a i : Deck d) = DeckGrid.step q d a (enum.symm i) := by
  by_cases h : enum.symm i = a.1 <;> simp [liftDirection,DeckGrid.step,productStep,h]

/-- All nonlocal public neighbor channels have genuine allowed integral moves.
The tile at their terminal endpoint is obtained by right multiplication. -/
noncomputable def gridRoutes {R : Type*} (table :
    (grid position input order (bits := bits) (s := s) (hops := hops) (copies := copies)).Tables R)
    {L : ℝ} (allows : ∀ a : I → gamma 1, a ≠ 1 → (∀ i, a i = 1 ∨ (a i).val ∈ routingGenerators) →
      a ∈ allowedMoves I L) : SiteRoutes (Pack.mk _ table) I z L := by
  let M := grid position input order (bits := bits) (s := s) (hops := hops) (copies := copies)
  let origin (v : M.Site) (i : I) := (v (enum.symm i)).out
  let active (e : M.Edge) := decide (DeckGrid.step q (z+1) e.2 ≠ 1)
  have lift (e : M.Edge) (ha : active e = true) : liftDirection enum e.2 ∈ allowedMoves I L := by
    apply allows
    · intro he
      have dne : DeckGrid.step q (z+1) e.2 ≠ 1 := of_decide_eq_true ha
      apply dne
      funext i
      have hi := liftDirection_reduce enum e.2 (z+1) (enum i)
      simpa [he] using hi.symm
    · intro i
      by_cases h : enum.symm i=e.2.1 <;> simp [liftDirection,h,e.2.2.property]
  refine ⟨origin,active,fun e he => ⟨_,lift e he⟩,?_⟩
  intro e he
  funext i
  change (↑(((e.1 * DeckGrid.step q (z+1) e.2) (enum.symm i)).out) : Deck (z+1)) =
    ↑((e.1 (enum.symm i)).out) * ↑(liftDirection enum e.2 i)
  rw [QuotientGroup.out_eq',QuotientGroup.out_eq',liftDirection_reduce]
  rfl

include enum in
/-- One catalog budget supplies these grid routes at every depth and for
arbitrary public widths and private site tables. -/
theorem exists_grid_budget (h : ℝ) : ∃ L > 0, ∀ {R : Type*}
    (table : (grid position input order (bits := bits) (s := s) (hops := hops) (copies := copies)).Tables R),
    ∃ r : SiteRoutes (Pack.mk _ table) I z L, ∀ c, r.active c = decide (DeckGrid.step q (z+1) c.2 ≠ 1) := by
  obtain ⟨L,hL,hgen,_⟩ := exists_move_budget (I := I) h
  exact ⟨L,hL,fun t => ⟨gridRoutes position input order enum t hgen,fun _ => rfl⟩⟩

end Shortening.PublicCapacity

end BorderVNP
end Computability
end OAI

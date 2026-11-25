import OAI.Computability.BorderVNP.PackedHistoryRouteRows
import OAI.Computability.BorderVNP.ShortenPublicBottomCapacity
import OAI.Computability.BorderVNP.DiagonalExternalSewFields

/-!
# Initial public route rows of the repeated physical grid

All geometric coordinates, endpoint pointers, widths and integral neighbor
steps of the bottom public layout are fixed before the profile input. Two
shared Boolean constants supply the literal bits of this routed grid.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Packing Cover Cover.AddressCircuit Crossing Epoch Shortening Shortening.PublicCapacity
open Shortening.PublicEndpoints VPVNP.VerifierNetwork Diagonal.ExternalSew.FieldExport
open scoped Classical

variable {D q d w : ℕ} {P K I : Type*} {bits : P → ℕ} [Fintype I] {L : ℝ}
    (enum : Fin q ≃ I) (p : Pack D P bits K) (r : SiteRoutes p I d L)
    {s : Shape} (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site)

/-- A routed public layout can be installed at the bottom of the history by
two shared constant gates. All vacant route names stay inactive. -/
theorem ready_constant_frames (σ : Type*) [Fintype σ]
    (fit : s.sites ≤ 2^w) (small : ∀ e, p.layout.width e < 2^w) :
    ∃ f : Frame σ (Pins (allowedMoves I L) q (d+1) s.sites s.edges w),
      f.size ≤ 2 ∧ ∀ x, Ready enum p r row dummy (f.eval x) := by
  let org (v : p.layout.Site) := productWires (d+1) (fun i => (r.origin v (enum i) : Deck (d+1)))
  let data := Function.extend row.site org (fun _ _ => false)
  let names := layoutInput p.layout row.site row.edge dummy w w data
  let act := Function.extend row.edge r.active (fun _ => false)
  let chosen (e : p.layout.Edge) (t : allowedMoves I L) :=
    if he : r.active e then decide (t = r.step e he) else false
  let move := Function.extend row.edge chosen (fun _ _ => false)
  let fixed : Pins (allowedMoves I L) q (d+1) s.sites s.edges w → Bool :=
    Sum.elim (fun j => Sum.elim (fun _ => decide (j.1 ∈ Set.range row.edge)) (move j.1) j.2)
      (Sum.elim act names)
  let f := (constants σ).select fun j => Sum.inr (fixed j)
  refine ⟨f,by simpa [f] using constants_size σ,?_⟩
  intro x
  have eq : f.eval x = fixed := by
    funext j
    rw [show f.eval x j = (constants σ).eval x (Sum.inr (fixed j)) from Frame.select_eval _ _ _ _,constants_eval]
    rfl
  rw [eq]
  refine ⟨represents_layoutInput p.layout row.site row.edge dummy data fit small,?_,?_,?_,?_,?_⟩
  · intro v j
    change data (row.site v) j = org v j
    exact congrFun (row.site.injective.extend_apply org (fun _ _ => false) v) j
  · intro i
    change decide (i ∈ Set.range row.edge) = true ↔ i ∈ Set.range row.edge
    simp
  · intro e
    change act (row.edge e) = r.active e
    exact row.edge.injective.extend_apply r.active (fun _ => false) e
  · intro i hi
    change act i = false
    exact Function.extend_apply' r.active (fun _ => false) i hi
  · intro e he t
    change move (row.edge e) t = decide (t = r.step e he)
    exact (congrFun (row.edge.injective.extend_apply chosen (fun _ _ => false) e) t).trans (by simp only [chosen,dite_eq_left he])

variable {J : Type} [Fintype J] (coords : Fin q ≃ J)
variable {z leaves copies lanes hops : ℕ} {Port : Type} {width : Port → ℕ}
    (position : (Fin q → Deck (z+1)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (input : Port ≃ Fin leaves) (order : Fin (Fintype.card (Fin q → Deck (z+1))) ≃ (Fin q → Deck (z+1)))

/-- Bottom of the actual repeated product-cover grid, with its explicit
generator lifts, stable tile/direction names and arbitrary private factors. -/
theorem grid_constant_frames (σ : Type*) [Fintype σ] (table :
    (grid position input order (bits := width) (s := lanes) (hops := hops) (copies := copies)).Tables K)
    (allows : ∀ a : J → gamma 1, a ≠ 1 → (∀ i, a i=1 ∨ (a i).val ∈ routingGenerators) → a ∈ allowedMoves J L)
    (fit : Fintype.card (Fin q → Deck (z+1)) ≤ 2^w)
    (small : ∀ e, (grid position input order (bits := width) (s := lanes) (hops := hops) (copies := copies)).width e < 2^w) :
    let N := grid position input order (bits := width) (s := lanes) (hops := hops) (copies := copies)
    let shape := gridShape (Fintype.card (Fin q → Deck (z+1))) (Fintype.card (DeckGrid.Direction q))
    let names := gridRows position input order (bits := width) (s := lanes) (hops := hops) (copies := copies)
    let route := gridRoutes position input order coords table allows
    ∃ f : Frame σ (Pins (allowedMoves J L) q (z+1) shape.sites shape.edges w),
      f.size ≤ 2 ∧ ∀ x, Ready coords (Pack.mk N table) route names (fun _ => (1 : Fin q → Deck (z+1))) (f.eval x) := by
  intro N shape names route
  exact ready_constant_frames coords (Pack.mk N table) route names (fun _ => (1 : Fin q → Deck (z+1))) σ fit small


/-- The same two-gate initializer works simultaneously for every coefficient
type and private assignment on the given public bottom grid. -/
theorem uniform_grid_constant_frames (σ : Type*) [Fintype σ]
    (allows : ∀ a : J → gamma 1, a ≠ 1 → (∀ i, a i=1 ∨ (a i).val ∈ routingGenerators) → a ∈ allowedMoves J L)
    (fit : Fintype.card (Fin q → Deck (z+1)) ≤ 2^w)
    (small : ∀ e, (grid position input order (bits := width) (s := lanes) (hops := hops) (copies := copies)).width e < 2^w) :
    let N := grid position input order (bits := width) (s := lanes) (hops := hops) (copies := copies)
    let shape := gridShape (Fintype.card (Fin q → Deck (z+1))) (Fintype.card (DeckGrid.Direction q))
    let names := gridRows position input order (bits := width) (s := lanes) (hops := hops) (copies := copies)
    ∃ f : Frame σ (Pins (allowedMoves J L) q (z+1) shape.sites shape.edges w),
      f.size ≤ 2 ∧ ∀ (R : Type*) (table : N.Tables R) x,
        Ready coords (Pack.mk N table) (gridRoutes position input order coords table allows)
          names (fun _ => (1 : Fin q → Deck (z+1))) (f.eval x) := by
  intro N shape names
  let zero : N.Tables Unit := default
  obtain ⟨f,cost,ready⟩ := grid_constant_frames coords position input order σ zero allows fit small
  refine ⟨f,cost,?_⟩
  intro R table x
  obtain ⟨ports,orig,present,active,hole,move⟩ := ready x
  exact ⟨ports,orig,present,active,hole,move⟩

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI

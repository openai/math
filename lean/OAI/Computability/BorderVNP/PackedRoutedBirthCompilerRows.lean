import OAI.Computability.BorderVNP.PackedCompilerRows
import OAI.Computability.BorderVNP.PackedGridOwnerBank

/-! # Compiler row bounds for the routed fine verifier at birth

Both original Boolean vertices and equality relays obey the same trivalence
bound. Staging and padding then give the initial row bounds for the concrete
box whose rules read the wired witness and its designated report positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse GridBoxes Inherited Shortening
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val) (copies capFine capReport : ℕ)
variable {K : Type*} [Field K] {m : ℕ} (e : PaidIdentity K D m)

/-- Trivalence supplies the full initial invariant of the actual stored site.
Its range includes the padding, staged unary checks and report sources. -/
theorem born_compilerRows (tri : N.Trivalent) :
    (born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID
      v rules copies capFine capReport).CompilerRows e := by
  obtain ⟨hs,hr⟩ := born_schema_rowBound N cell position pack width owner lane aligned
    siteID edgeID portID channelID groupID v rules copies capFine capReport
  apply Site.CompilerRows.of_initial e hs hr
  exact born_tableBound N cell position pack width owner lane aligned siteID edgeID portID channelID groupID
    v rules copies capFine capReport (fun u => (N.lane_count_le tri.1 u).trans (tri.2 u))

end Packing.BottomGridBank

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes Diagonal.CellEntries GridPlacement Cover TeamContraction Shortening
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Equality of deck positions used by the wired verifier's path subdivision. -/
noncomputable local instance routedCompilerDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

/-- The input to the concrete bottom box remains trivalent at every site
after subdivision along the paths of the chosen verifier witness. -/
theorem routedFine_trivalent : (W.routedFine position).Trivalent :=
  (wiredFine G d D W.trees).trivalent_subdivide
    (BooleanLayout.trivalent (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d))
    (wireRoutes position W.route)

variable {C Q A : Type} [Fintype C] [Fintype Q] [Fintype A] {H : ℕ} {src dst : Q → C}
variable (N : Network D (Fin r × Fin (publicWidth G)) (fun _ => 1))
    (atSite : N.Site → C) (pos : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (pack : (N.cellNetwork atSite pos).ChannelPacking src dst H)
    (width : A → ℕ) (owner : A → C) (lane : (Fin r × Fin (publicWidth G)) ↪ (a : A) × Fin (width a))
    (aligned : ∀ p, owner (lane p).1 = atSite (N.attach p))
    {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa)
    (v : C) (rules : ∀ u : {u : N.Site // atSite u = v}, Rule N u.val)
    {K : Type*} [Field K] {m : ℕ} (e : PaidIdentity K D m)

/-- A bottom bank on the true routed verifier obeys the fixed compiler bounds
for every chosen cell, rule list, and multiplicity. The network parameter lets
callers use the definitionally identical network in their physical layout. -/
theorem seedBorn_compilerRows (hN : N = W.routedFine position) (copies capFine capReport : ℕ) :
    (BottomGridBank.born N atSite pos pack width owner lane aligned siteID edgeID portID
      channelID groupID v rules copies capFine capReport).CompilerRows e :=
  BottomGridBank.born_compilerRows N atSite pos pack width owner lane aligned siteID edgeID portID
    channelID groupID v rules copies capFine capReport e (hN.symm ▸ W.routedFine_trivalent position)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI

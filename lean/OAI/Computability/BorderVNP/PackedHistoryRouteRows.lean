import OAI.Computability.BorderVNP.ShortenPublicRelativeCharged
import OAI.Computability.BorderVNP.ShortenPublicSubdivisionRows

/-! # Public site-route rows passed between physical epochs

The move field is a finite relative table index. Addresses use actual deck
coordinates at the current level. Each physical cable, including a frozen
or zero-width one, keeps its own public occupancy bit and endpoint pointers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Crossing Cover Cover.AddressCircuit Epoch
open Shortening.PublicEndpoints Shortening.PublicSegments VPVNP.VerifierNetwork
open scoped Classical

/-- Per-cable occupancy and one-hot moves, followed by the charge mask, site
address bank, and stable endpoint and width columns. -/
abbrev Pins (Move : Type*) (q l V E w : ℕ) :=
  (Fin E × (Unit ⊕ Move)) ⊕ Raw (ProductSlots q l) V E w w

variable {D q d w : ℕ} {P : Type*} {K : Type*} {bits : P → ℕ} {I : Type*} [Fintype I] {L : ℝ}
    (enum : Fin q ≃ I) (p : Pack D P bits K) (r : SiteRoutes p I d L) {s : Shape}
    (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site)

/-- A public physical boundary represents the chosen integral motion of each
nonlocal cable and all stable names and pointers of the routed pack. -/
structure Ready (x : Pins (allowedMoves I L) q (d+1) s.sites s.edges w → Bool) : Prop where
  /-- Dynamic source, target and width values for all rows, including holes. -/
  names : PublicEndpoints.Represents p.layout row.site row.edge dummy (fun j => x (.inr (.inr j)))
  /-- The old site position supplies the reduced integral origin, in the specified factor order. -/
  origins : ∀ v j, x (.inr (.inr (.inl (row.site v,j)))) =
    productWires (d+1) (fun i => (r.origin v (enum i) : Deck (d+1))) j
  /-- Every original cable has its public row, including a real wire of width zero. -/
  present : ∀ i, x (.inl (i,.inl ())) = true ↔ i ∈ Set.range row.edge
  /-- The subdivision decision for each real cable is exactly the chosen site routing. -/
  active : ∀ e, x (.inr (.inl (row.edge e))) = r.active e
  /-- A vacant stripe receives no subdivisions. -/
  hole : ∀ i, i ∉ Set.range row.edge → x (.inr (.inl i)) = false
  /-- The finite move selector identifies the exact integral motion on each active cable. -/
  move : ∀ e (he : r.active e) t, x (.inl (row.edge e,.inr t)) = decide (t = r.step e he)

/-- A shared endpoint lookup, together with the original route row inputs. -/
noncomputable def endpoints (q d V E w : ℕ) (Move : Type*) [Fintype Move] (fit : V ≤ 2^w) :
    Frame (Pins Move q d V E w) (Pins Move q d V E w ⊕ ((Fin E × Bool) × ProductSlots q d)) :=
  (((PublicEndpoints.join (ProductSlots q d) w fit).select Sum.inr).subst
    (Frame.initial fun j => .inr (.inr j))).withInput

/-- The product address joined from the source (or target) of a physical cable. -/
theorem endpoints_origin {x : Pins (allowedMoves I L) q (d+1) s.sites s.edges w → Bool}
    (ready : Ready enum p r row dummy x) (fit : s.sites ≤ 2^w) (e : p.layout.Edge) (side : Bool) (j : ProductSlots q (d+1)) :
    (endpoints q (d+1) s.sites s.edges w (allowedMoves I L) fit).eval x (.inr ((row.edge e,side),j)) =
      productWires (d+1) (fun i => (r.origin (if side then p.layout.src e else p.layout.dst e) (enum i) : Deck (d+1))) j := by
  let vals := fun v : PublicEndpoints.Inputs (ProductSlots q (d+1)) s.sites s.edges w w => x (.inr (.inr v))
  have hx : (Frame.initial fun v : PublicEndpoints.Inputs (ProductSlots q (d+1)) s.sites s.edges w w =>
      (.inr (.inr v) : Pins (allowedMoves I L) q (d+1) s.sites s.edges w)).eval x = vals := funext fun _ => by simp [vals]
  have he := PublicEndpoints.join_occupied p.layout row.site row.edge dummy fit ready.names e
  simp only [endpoints,Frame.withInput_eval_inr,Frame.subst_eval,Frame.select_eval,hx]
  cases side
  · exact (he.2.1 j).trans (ready.origins _ j)
  · exact (he.1 j).trans (ready.origins _ j)

/-- Only the single sparse batched join is charged for the dynamic endpoint addresses. -/
theorem endpoints_size (q d V E w : ℕ) (Move : Type*) [Fintype Move] (fit : V ≤ 2^w) :
    (endpoints q d V E w Move fit).size ≤
      300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+w+Fintype.card (ProductSlots q d)+1)^3 := by
  simpa [endpoints] using PublicEndpoints.join_size (cables := E) (ProductSlots q d) w fit

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI

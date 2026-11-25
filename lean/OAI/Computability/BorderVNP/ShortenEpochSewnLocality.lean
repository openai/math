import OAI.Computability.BorderVNP.ShortenEpochNeighbors
import OAI.Computability.BorderVNP.ShortenEpochSewnConcentration
import OAI.Computability.BorderVNP.ShortenAddressQuotient

/-!
# Midpoint locality for the quotient profile

No common lift of the pack is required. The seed's inserted sites share
one local chart, and each old endpoint has its own close lift. The quotient
projection contracts distances. These facts place each new midpoint in the
bounded deck neighborhood of the seed's donor tile, independently of the
profile and of the number of slots in the old cable interval.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Epoch Cover Crossing Finset
open scoped Classical

variable {I B : Type} [Fintype I] [Fintype B] {D : ℕ} {d : ℕ}

/-- Any internal profile cable, including selector and feeder cables,
has its quotient midpoint within twice the radius of the projected center. -/
theorem SeedChart.internal_midpoint_distance (c : SeedChart I D) (hr : 0 ≤ c.radius)
    (π : HyperbolicHost I → SurfaceHost I (d+1)) (hπ : ∀ x y, dist (π x) (π y) ≤ dist x y)
    (v w : EuclideanSpace ℝ (Fin D)) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    {mid : SurfaceHost I (d+1)} (hm : dist mid (π (c.atSite v)) ≤
      dist (π (c.atSite v)) (π (c.atSite w)) / 2) :
    dist mid (π c.center) ≤ 2*c.radius := by
  have h1 := (hπ _ _).trans (Epoch.SeedChart.dist_atSite_center c hr v hv)
  have h2 := (hπ _ _).trans (Epoch.SeedChart.dist_atSite_center c hr w hw)
  simpa using midpoint_near_center (err := 0) h1 (by simpa using h2) hm

/-- A hook joins an inserted site to the projection of a separately lifted
old endpoint. Its midpoint is in the same bounded deck neighborhood. -/
theorem SeedChart.hook_midpoint_distance (c : SeedChart I D) (hr : 0 ≤ c.radius)
    (π : HyperbolicHost I → SurfaceHost I (d+1)) (hπ : ∀ x y, dist (π x) (π y) ≤ dist x y)
    (v : EuclideanSpace ℝ (Fin D)) (hv : ‖v‖ ≤ 1) (terminal : Fin D × Bool)
    (lift : HyperbolicHost I) {err : ℝ} (hclose : dist lift (c.atTerminal terminal) ≤ err)
    {mid : SurfaceHost I (d+1)} (hm : dist mid (π (c.atSite v)) ≤
      dist (π (c.atSite v)) (π lift) / 2) :
    dist mid (π c.center) ≤ 2*c.radius + err/2 := by
  apply midpoint_near_center ((hπ _ _).trans (Epoch.SeedChart.dist_atSite_center c hr v hv)) _ hm
  apply (hπ _ _).trans
  have h := dist_triangle lift (c.atTerminal terminal) c.center
  rw [Epoch.SeedChart.dist_atTerminal_center c hr] at h
  linarith

set_option maxHeartbeats 1000000 in
/-- For a fixed locality radius, both the degree of the tile-address relation
and its reverse degree have uniform bounds at all quotient levels. Any chosen
pair of points in this radius automatically meets the membership requirement
of the sewn-profile concentration theorem. -/
theorem quotient_seed_neighbors (ρ : ℝ) :
    ∃ M : ℕ, ∀ d, ∃ near : (I → Deck (d+1)) → Finset ((I → Deck (d+1)) × B),
      (∀ o, (near o).card ≤ M * Fintype.card B) ∧
      (∀ a, (univ.filter fun o => a ∈ near o).card ≤ M) ∧
      ∀ x y : SurfaceHost I (d+1), dist x y ≤ ρ → ∀ b : B,
        (productTileName d x,b) ∈ near (productTileName d y) := by
  obtain ⟨M,hM⟩ := exists_local_deck_moves (I := I) ρ
  refine ⟨M,?_⟩
  intro d
  obtain ⟨moves,hcard,h⟩ := hM d
  refine ⟨donorNeighbors moves,fun o => (donorNeighbors_card moves o).trans
    (Nat.mul_le_mul_right _ hcard),?_,?_⟩
  · intro a
    convert! (donorNeighbors_fanOut moves a).trans hcard using 2
    ext o
    simp
  · intro x y hxy b
    obtain ⟨m,hm,he⟩ := h x y hxy
    exact mem_donorNeighbors moves hm he

end Shortening

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.CoverSiteRounding
import OAI.Computability.BorderVNP.CoverLorentzProduct
import OAI.Computability.BorderVNP.ShortenAddressCost

/-!
# Uniformly bounded neighborhoods for the concrete output midpoints

The same finite list of relative deck moves works on every sufficiently deep
level. A source and destination within a fixed radius have tile addresses
related by one such move per surface factor. In particular, expanding a seed
into its actual paid profile changes the tile concentration by a bounded
factor independent of the number of tiles and of the wire widths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Cover Shortening Crossing Finset
open scoped Classical

variable {I T B : Type*} [Fintype I] [Group T] [Fintype T] [Fintype B]

/-- Donor addresses for an output tile: all relative bins of any tile that can
reach the output by one of the finite list of local moves. -/
noncomputable def donorNeighbors (moves : Finset T) (o : T) : Finset (T × B) :=
  (moves.image (fun m => o*m⁻¹)) ×ˢ Finset.univ

omit [Fintype T] in
/-- The number of eligible donor addresses is uniform in the output tile. -/
theorem donorNeighbors_card (moves : Finset T) (o : T) :
    (donorNeighbors (B := B) moves o).card ≤ moves.card * Fintype.card B := by
  rw [donorNeighbors, card_product, card_univ]
  exact Nat.mul_le_mul_right _ card_image_le

omit [Fintype T] in
/-- A local move puts the donor in the destination's bounded list. -/
theorem mem_donorNeighbors (moves : Finset T) {m : T} (hm : m ∈ moves) {a : T × B} {o : T}
    (ho : o = a.1*m) : a ∈ donorNeighbors moves o :=
  mem_product.mpr ⟨mem_image.mpr ⟨m,hm,by rw [ho,mul_inv_cancel_right]⟩,mem_univ _⟩

/-- Each donor can enter at most one output tile per move. -/
theorem donorNeighbors_fanOut (moves : Finset T) (a : T × B) :
    (univ.filter fun o => a ∈ donorNeighbors moves o).card ≤ moves.card := by
  apply (card_le_card (t := moves.image (fun m => a.1*m)) ?_).trans card_image_le
  intro o ho
  obtain ⟨m,hm,ha⟩ := mem_image.mp (mem_product.mp (mem_filter.mp ho).2).1
  exact mem_image.mpr ⟨m,hm,by rw [← ha,inv_mul_cancel_right]⟩

variable {d : ℕ}

/-- The tile name of a position in the product quotient. -/
noncomputable def productTileName (d : ℕ) (x : SurfaceHost I (d+1)) : I → Deck (d+1) :=
  fun i => surfaceAddress d (x i)

/-- A single multiplicity bound works for the tile names of all nearby point
pairs in every cover, including product directions with zero components. -/
theorem exists_local_deck_moves (ρ : ℝ) :
    ∃ M : ℕ, ∀ d, ∃ moves : Finset (I → Deck (d+1)), moves.card ≤ M ∧
      ∀ x y : SurfaceHost I (d+1), dist x y ≤ ρ →
        ∃ m ∈ moves, productTileName d y = productTileName d x * m := by
  classical
  obtain ⟨_,base,_,_,h⟩ := finite_rounding_moves ρ
  refine ⟨base.card ^ Fintype.card I, ?_⟩
  intro d
  let project (f : I → ↥base) (i : I) : Deck (d+1) := ((f i).val : Deck (d+1))
  let moves := univ.image project
  refine ⟨moves,?_,?_⟩
  · exact card_image_le.trans (by simp)
  · intro x y hxy
    choose m hm he using fun i => h d (x i) (y i) ((PiLp.dist_apply_le x y i).trans hxy)
    let f (i : I) : ↥base := ⟨m i,hm i⟩
    exact ⟨project f,mem_image_of_mem _ (mem_univ f),funext he⟩

variable {D : ℕ}

/-- Every inserted site, including local selector boxes, lies within one
radius of the representative crossing center in the lifted hyperbolic host. -/
theorem SeedChart.dist_atSite_center (c : SeedChart I D) (hr : 0 ≤ c.radius)
    (z : EuclideanSpace ℝ (Fin D)) (hz : ‖z‖ ≤ 1) : dist (c.atSite z) c.center ≤ c.radius := by
  rw [show c.center = shiftTo c.center (productChart 0) from (shiftTo_chart_zero _).symm]
  change dist (shiftTo c.center (productChart (c.radius • c.axes z)))
    (shiftTo c.center (productChart 0)) ≤ _
  rw [(shiftTo_isometry _).dist_eq]
  apply (productChart_dist_le _ _).trans
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,c.axes.norm_map]
  exact mul_le_of_le_one_right hr hz

/-- The intended geodesic terminal is exactly one radius from the seed center. -/
theorem SeedChart.dist_atTerminal_center (c : SeedChart I D) (hr : 0 ≤ c.radius)
    (p : Fin D × Bool) : dist (c.atTerminal p) c.center = c.radius := by
  have h0 (u : PiLp 2 (fun _ : I => ℂ)) : productLine u 0 = productChart 0 := by
    ext1 i
    change tangentLine (unitDirection (u i)) (0 * ‖u i‖) = tangentChart 0
    simp [tangentLine]
  let v := c.axes (antipodalPosition p)
  have hv : ‖v‖ = 1 := by
    rw [show ‖v‖ = ‖antipodalPosition p‖ from c.axes.norm_map _]
    rcases p with ⟨i,b⟩; cases b <;> simp [antipodalPosition]
  calc
    _ = dist (shiftTo c.center (productLine v c.radius)) (shiftTo c.center (productLine v 0)) := by
      rw [h0,shiftTo_chart_zero]; rfl
    _ = _ := by rw [(shiftTo_isometry _).dist_eq,dist_productLine,sub_zero,abs_of_nonneg hr,hv,mul_one]

/-- A midpoint of a new quotient cable stays within a bounded neighborhood
when both endpoints are near the representative. This needs only the two
actual endpoint distances; the network may have cycles winding in the quotient. -/
theorem midpoint_near_center {Q : Type*} [PseudoMetricSpace Q] {a b o mid : Q}
    {r err : ℝ} (ha : dist a o ≤ r) (hb : dist b o ≤ r+err)
    (hm : dist mid a ≤ dist a b / 2) :
    dist mid o ≤ 2*r + err/2 := by
  have htriangle := dist_triangle a o b
  rw [dist_comm o b] at htriangle
  linarith only [dist_triangle mid a o, htriangle,ha,hb,hm]

end Epoch

end BorderVNP
end Computability
end OAI

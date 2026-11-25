import OAI.Computability.BorderVNP.CoverSurfaceMotionDegree
import OAI.Computability.BorderVNP.CoverSiteRounding

/-!
# Uniform fan-in and fan-out at the final site rounding

Fix a segment radius and a denominator. The source point determines one source
site, and the motion sends its neighborhood into a bounded neighborhood of
the image of that site. Conversely, every destination site has a fixed finite
number of inverse images. Lifting its neighborhood to those points bounds
the number of possible source tiles independently of the level and pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Finset Set UpperHalfPlane BorderVNP.Cover.Frame
open scoped Classical

/-- The surface address at any specified positive level, including noncanonical sums
of depths. -/
noncomputable def addressAt : (d : ℕ) → 0 < d → Surface d → Deck d
  | 0, h => False.elim (Nat.lt_irrefl 0 h)
  | d+1, _ => surfaceAddress d

/-- The surface site of an address at any positive level. -/
noncomputable def siteAt : (d : ℕ) → 0 < d → Deck d → Surface d
  | 0, h => False.elim (Nat.lt_irrefl 0 h)
  | d+1, _ => deckSite d

/-- Every endpoint is within a fixed distance of its own site, uniformly in the depth. -/
theorem uniform_site_distance : ∃ R ≥ (0:ℝ), ∀ d (x : Surface (d+1)), dist x (roundedSite d x) ≤ R := by
  obtain ⟨R,hR,hb⟩ := dirichlet_bounded 1
  refine ⟨R,hR,?_⟩
  rintro d ⟨x⟩
  let u := Frame.toBaseTile x
  change dist (projectPoint _ x) (projectPoint _ (gammaSL 1 u⁻¹ • I)) ≤ R
  apply (dist_projectPoint_le _ _ _).trans
  rw [← dist_smul (gammaSL 1 u),map_inv,smul_inv_smul]
  exact hb (toBaseTile_mem x).1

private theorem site_distance_all : ∃ R ≥ (0:ℝ), ∀ l (hl : 0 < l) (x : Surface l),
    dist x (siteAt l hl (addressAt l hl x)) ≤ R := by
  obtain ⟨R,hR,h⟩ := uniform_site_distance
  refine ⟨R,hR,?_⟩
  rintro (_|l) hl x
  · omega
  · exact h l x

private theorem rounding_moves_all (r : ℝ) : ∃ M : Finset (gamma 1), ∀ l (hl : 0 < l)
    (x y : Surface l), dist x y ≤ r → ∃ m ∈ M,
      addressAt l hl y = addressAt l hl x * (m : Deck l) := by
  obtain ⟨_,M,_,_,h⟩ := finite_rounding_moves r
  refine ⟨M,?_⟩
  rintro (_|l) hl x y hxy
  · omega
  · exact h l x y hxy

/-- Uniform forward and inverse tile neighborhoods for moving all points within `ρ`
of a source point. The choices cover every possible source and endpoint at once. -/
theorem single_motion_neighbors (ρ : ℝ) (a : ℕ) : ∃ N : ℕ, ∀ d {g : SL} (hg : Clears g a),
    ∃ (forward : Deck (d+2+2*a) → Finset (Deck (d+2)))
      (backward : Deck (d+2) → Finset (Deck (d+2+2*a))),
      (∀ s, (forward s).card ≤ N) ∧ (∀ t, (backward t).card ≤ N) ∧
      ∀ x y : Surface (d+2+2*a), dist x y ≤ ρ →
        let s := addressAt (d+2+2*a) (by omega) x
        let t := addressAt (d+2) (by omega) (surfaceMotion hg (d+2) y)
        t ∈ forward s ∧ s ∈ backward t := by
  classical
  obtain ⟨R,_,hR⟩ := site_distance_all
  obtain ⟨M,hM⟩ := rounding_moves_all (R+ρ)
  let D : ℕ := (7^3)^(2*a)
  refine ⟨D*M.card,?_⟩
  intro d g hg
  let inLevel := d+2+2*a
  let outLevel := d+2
  let f := surfaceMotion hg (d+2)
  let X (t : Deck (d+2)) := {z : Surface (d+2+2*a) // f z = siteAt outLevel (by dsimp [outLevel]; omega) t}
  have hx (t : Deck (d+2)) : Nat.card (X t) = D := surfaceMotion_card hg d _
  let finX (t : Deck (d+2)) : Fintype (X t) := by
    have : Finite (X t) := Nat.finite_of_card_ne_zero ((hx t).trans_ne (by dsimp [D]; positivity))
    exact Fintype.ofFinite _
  let forward (s : Deck (d+2+2*a)) := M.image (fun m : gamma 1 =>
    addressAt outLevel (by dsimp [outLevel]; omega) (f (siteAt inLevel (by dsimp [inLevel]; omega) s)) * (m : Deck (d+2)))
  let backward (t : Deck (d+2)) := (Finset.univ : Finset (X t × ↥M)).image
    (fun p => addressAt inLevel (by dsimp [inLevel]; omega) p.1.val * (p.2.val : Deck (d+2+2*a)))
  refine ⟨forward,backward,?_,?_,?_⟩
  · intro s
    exact card_image_le.trans (Nat.le_mul_of_pos_left _ (by dsimp [D]; positivity))
  · intro t
    have hc : Fintype.card (X t) = D := (Nat.card_eq_fintype_card.symm).trans (hx t)
    exact card_image_le.trans (by simp [hc])
  · intro x y hxy
    dsimp only
    let z := f y
    let S := addressAt inLevel (by dsimp [inLevel]; omega) x
    let T := addressAt outLevel (by dsimp [outLevel]; omega) z
    have hforward : dist (f (siteAt inLevel (by dsimp [inLevel]; omega) S)) z ≤ R+ρ := by
      apply (surfaceMotion_dist_le hg _ _ _).trans
      have hxR := hR inLevel (by dsimp [inLevel]; omega) x
      rw [dist_comm] at hxR
      exact (dist_triangle _ x y).trans (add_le_add hxR hxy)
    obtain ⟨m,hm,e⟩ := hM outLevel (by dsimp [outLevel]; omega) _ _ hforward
    have hback : siteAt outLevel (by dsimp [outLevel]; omega) T ∈ Metric.closedBall (f x) (R+ρ) := by
      have hzR := hR outLevel (by dsimp [outLevel]; omega) z
      rw [dist_comm] at hzR
      have hzX : dist z (f x) ≤ ρ := by
        rw [dist_comm]; exact (surfaceMotion_dist_le hg _ _ _).trans hxy
      exact (dist_triangle _ z _).trans (add_le_add hzR hzX)
    rw [← surfaceMotion_closedBall hg (d+2) x] at hback
    obtain ⟨w,hw,hwf⟩ := hback
    obtain ⟨v,hv,ev⟩ := hM inLevel (by dsimp [inLevel]; omega) w x hw
    exact ⟨mem_image.mpr ⟨m,hm,e.symm⟩,
      mem_image.mpr ⟨(⟨w,hwf⟩,⟨v,hv⟩),mem_univ _,ev.symm⟩⟩

/-- The same relation simultaneously controls all coordinates of the product host. -/
private theorem product_neighbors (ρ : ℝ) (a : ℕ) (I : Type*) [Fintype I] [DecidableEq I] : ∃ N : ℕ,
    ∀ d (g : I → SL) (hg : ∀ k, Clears (g k) a),
      ∃ sources : (I → Deck (d+2)) → Finset (I → Deck (d+2+2*a)),
        (∀ t, (sources t).card ≤ N) ∧
        (∀ s, (Finset.univ.filter fun t => s ∈ sources t).card ≤ N) ∧
        ∀ x y : I → Surface (d+2+2*a), (∀ k, dist (x k) (y k) ≤ ρ) →
          (fun k => addressAt (d+2+2*a) (by omega) (x k)) ∈
            sources (fun k => addressAt (d+2) (by omega) (surfaceMotion (hg k) (d+2) (y k))) := by
  classical
  obtain ⟨B,hB⟩ := single_motion_neighbors ρ a
  refine ⟨B^(Fintype.card I),?_⟩
  intro d g hg
  choose f b hf hb hr using fun k => hB d (hg k)
  let src (t : I → Deck (d+2)) := (Fintype.piFinset (fun k => b k (t k))).filter
    fun s => ∀ k, t k ∈ f k (s k)
  refine ⟨src,?_,?_,?_⟩
  · intro t
    apply (card_filter_le _ _).trans
    rw [Fintype.card_piFinset,← Finset.card_univ,← Finset.prod_const]
    exact prod_le_prod fun k _ => hb k _
  · intro s
    apply (card_le_card (t := Fintype.piFinset (fun k => f k (s k))) ?_).trans
    · rw [Fintype.card_piFinset,← Finset.card_univ,← Finset.prod_const]
      exact prod_le_prod fun k _ => hf k _
    · intro t ht
      exact Fintype.mem_piFinset.mpr (mem_filter.mp (mem_filter.mp ht).2).2
  · intro x y hxy
    exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun k => (hr k _ _ (hxy k)).2),
      fun k => (hr k _ _ (hxy k)).1⟩

/-- The same relation simultaneously controls all coordinates of the product host. -/
theorem finite_product_motion_neighbors (ρ : ℝ) (a : ℕ) (I : Type*) [Fintype I] : ∃ N : ℕ,
    ∀ d (g : I → SL) (hg : ∀ k, Clears (g k) a),
      ∃ sources : (I → Deck (d+2)) → Finset (I → Deck (d+2+2*a)),
        (∀ t, (sources t).card ≤ N) ∧
        (∀ s, (Finset.univ.filter fun t => s ∈ sources t).card ≤ N) ∧
        ∀ x y : I → Surface (d+2+2*a), (∀ k, dist (x k) (y k) ≤ ρ) →
          (fun k => addressAt (d+2+2*a) (by omega) (x k)) ∈
            sources (fun k => addressAt (d+2) (by omega) (surfaceMotion (hg k) (d+2) (y k))) :=
  product_neighbors ρ a I

/-- The same relation simultaneously controls all coordinates of the product host. -/
theorem product_motion_neighbors (ρ : ℝ) (a q : ℕ) : ∃ N : ℕ,
    ∀ d (g : Fin q → SL) (hg : ∀ k, Clears (g k) a),
      ∃ sources : (Fin q → Deck (d+2)) → Finset (Fin q → Deck (d+2+2*a)),
        (∀ t, (sources t).card ≤ N) ∧
        (∀ s, (Finset.univ.filter fun t => s ∈ sources t).card ≤ N) ∧
        ∀ x y : Fin q → Surface (d+2+2*a), (∀ k, dist (x k) (y k) ≤ ρ) →
          (fun k => addressAt (d+2+2*a) (by omega) (x k)) ∈
            sources (fun k => addressAt (d+2) (by omega) (surfaceMotion (hg k) (d+2) (y k))) :=
  product_neighbors ρ a (Fin q)

end Cover

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.CoverLorentzSurface
import OAI.Computability.BorderVNP.CoverRelativePlacement
import OAI.Computability.BorderVNP.CoverDeckTower
import OAI.Computability.BorderVNP.ShortenEpochDirichlet

/-!
# Rounding endpoints to sites of the congruence quotient

The chosen Borel base tile resolves seams before passing to finite covers.
Each point has an equivariant integral address and a position relative to
its tile. If the sites of two nearby points differ, a closest lift of the
second point, translated by the address of the first, leaves the base tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set UpperHalfPlane MeasureTheory
open scoped ENNReal

private def includeLevel (d : ℕ) : gamma (d+1) →* gamma 1 :=
  Subgroup.inclusion (gamma_le_one d)

private theorem project_includeLevel (d : ℕ) (a : gamma (d+1)) :
    ((includeLevel d a : gamma 1) : Deck (d+1)) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr a.property

/-- The deck address of the tile containing the point of the level-`d+1` surface. -/
noncomputable def surfaceAddress (d : ℕ) : Surface (d+1) → Deck (d+1) :=
  Quotient.lift (fun z => ((Frame.toBaseTile z)⁻¹ : gamma 1)) (by
    rintro x _ ⟨a,rfl⟩
    change ((Frame.toBaseTile x)⁻¹ : Deck (d+1)) =
      (((Frame.toBaseTile (gammaSL 1 (includeLevel d a) • x))⁻¹ : gamma 1) : Deck (d+1))
    rw [Frame.toBaseTile_smul,_root_.mul_inv_rev,inv_inv]
    simp only [QuotientGroup.mk_mul, project_includeLevel, one_mul, QuotientGroup.mk_inv])

/-- The position in the base tile relative to the deck address. -/
noncomputable def relativePosition (d : ℕ) : Surface (d+1) → ℍ :=
  Quotient.lift (fun z => gammaSL 1 (Frame.toBaseTile z) • z) (by
    rintro x _ ⟨a,rfl⟩
    change _ = gammaSL 1 (Frame.toBaseTile (gammaSL 1 (includeLevel d a) • x)) •
      (gammaSL 1 (includeLevel d a) • x)
    rw [Frame.toBaseTile_smul,map_mul,map_inv,mul_smul,inv_smul_smul])

/-- The chosen representative for any point of the quotient lies in the canonical tile. -/
theorem relativePosition_mem (d : ℕ) (x : Surface (d+1)) : relativePosition d x ∈ planeTile 0 := by
  rcases x with ⟨x⟩
  exact Frame.toBaseTile_mem x

/-- The site belonging to a given deck address. -/
noncomputable def deckSite (d : ℕ) : Deck (d+1) → Surface (d+1) :=
  Quotient.lift (fun a : gamma 1 => projectPoint (d+1) (gammaSL 1 a • I)) (by
    intro a b h
    have h' := QuotientGroup.leftRel_apply.mp h
    have h'' : b.val * a.val⁻¹ ∈ gamma (d+1) := (gammaNormal _).mem_comm h'
    let c : gamma (d+1) := ⟨_, h''⟩
    apply Quotient.sound
    refine ⟨c,?_⟩
    change gammaSL 1 (b*a⁻¹) • (gammaSL 1 a • I) = _
    simp [mul_smul])

/-- Round a surface endpoint to its tile's distinguished site. -/
noncomputable def roundedSite (d : ℕ) (x : Surface (d+1)) : Surface (d+1) :=
  deckSite d (surfaceAddress d x)

/-- Distinct endpoint sites force a point outside the canonical tile at distance no
greater than the segment length from the first endpoint's relative position. -/
theorem exists_outside_of_rounding {d : ℕ} {x y : Surface (d+1)} {r : ℝ}
    (hr : dist x y ≤ r) (hne : roundedSite d x ≠ roundedSite d y) :
    ∃ v : ℍ, v ∉ planeTile 0 ∧ dist (relativePosition d x) v ≤ r := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  obtain ⟨a,ha⟩ := orbitDistance_attained (d+1) x y
  let w := gammaSL (d+1) a • y
  let u := Frame.toBaseTile x
  refine ⟨gammaSL 1 u • w, ?_, ?_⟩
  · intro hw
    have hu : Frame.toBaseTile w = u :=
      (existsUnique_mem_planeTile 0 w).unique (Frame.toBaseTile_mem w) hw
    have he : projectPoint (d+1) y = projectPoint (d+1) w := Quotient.sound ⟨a,rfl⟩
    apply hne
    change roundedSite d (projectPoint (d+1) x) = roundedSite d (projectPoint (d+1) y)
    rw [he]
    change deckSite d (((Frame.toBaseTile x)⁻¹ : gamma 1) : Deck (d+1)) =
      deckSite d (((Frame.toBaseTile w)⁻¹ : gamma 1) : Deck (d+1))
    rw [hu]
  · change dist (gammaSL 1 u • x) (gammaSL 1 u • w) ≤ r
    rw [dist_smul, ← ha]
    exact hr

/-- A single measurable test for a given radius covers every distinct-site rounding
event, simultaneously for all congruence levels. Its area grows at most linearly. -/
theorem surface_rounding_test : ∃ C ≥ (0 : ℝ), ∀ r > (0 : ℝ), 4*r ≤ 1 →
    ∃ S : Set ℍ, IsOpen S ∧ volume (frontier S) = 0 ∧ volume S ≤ ENNReal.ofReal (C*r) ∧
      ∀ d (x y : Surface (d+1)), dist x y ≤ r → roundedSite d x ≠ roundedSite d y →
        relativePosition d x ∈ S := by
  obtain ⟨C,hC,hs⟩ := Epoch.exists_planeTile_rounding_test 0
  refine ⟨C,hC,?_⟩
  intro r hr hr'
  obtain ⟨S,ho,hn,hm,hcover⟩ := hs r hr hr'
  refine ⟨S,ho,hn,hm,?_⟩
  intro d x y hxy hne
  obtain ⟨v,hv,hd⟩ := exists_outside_of_rounding hxy hne
  exact hcover _ (relativePosition_mem _ _) v (fun h => hv (interior_subset h)) hd

/-- There is one finite list of allowed site moves for every cover level. It covers
rounding of all pairs at distance at most a fixed radius. -/
theorem finite_rounding_moves (h : ℝ) : ∃ (R : ℝ) (M : Finset (gamma 1)), 0 ≤ R ∧
    (∀ a ∈ M, dist I (gammaSL 1 a • I) ≤ 2*R+h) ∧
    ∀ d (x y : Surface (d+1)), dist x y ≤ h →
      ∃ a ∈ M, surfaceAddress d y = surfaceAddress d x * (a : Deck (d+1)) := by
  classical
  obtain ⟨R,hR,hbound⟩ := dirichlet_bounded 1
  let B := Metric.closedBall I (2*R+h)
  let hm := finite_sites 1 (ProperSpace.isCompact_closedBall I (2*R+h))
  refine ⟨R,hm.toFinset,hR,?_,?_⟩
  · intro a ha
    rw [dist_comm]
    exact hm.mem_toFinset.mp ha
  · rintro d ⟨x⟩ ⟨y⟩ hxy
    obtain ⟨u,hu⟩ := orbitDistance_attained (d+1) x y
    let w := gammaSL (d+1) u • y
    let b := Frame.toBaseTile x
    let c := Frame.toBaseTile w
    have hw : projectPoint (d+1) y = projectPoint (d+1) w := Quotient.sound ⟨u,rfl⟩
    have hb : dist (gammaSL 1 b • x) I ≤ R := hbound (Frame.toBaseTile_mem x).1
    have hc : dist (gammaSL 1 c • w) I ≤ R := hbound (Frame.toBaseTile_mem w).1
    have he : dist (gammaSL 1 b • w) (gammaSL 1 b • x) ≤ h := by
      rw [dist_smul,dist_comm]
      exact hu ▸ hxy
    refine ⟨b*c⁻¹,hm.mem_toFinset.mpr ?_,?_⟩
    · change dist (gammaSL 1 (b*c⁻¹) • I) I ≤ 2*R+h
      have e : dist (gammaSL 1 (b*c⁻¹) • I) (gammaSL 1 b • w) ≤ R := by
        rw [map_mul,map_inv,mul_smul,dist_smul,← dist_smul (gammaSL 1 c),smul_inv_smul,dist_comm]
        exact hc
      linarith [dist_triangle (gammaSL 1 (b*c⁻¹) • I) (gammaSL 1 b • w) (gammaSL 1 b • x),
        dist_triangle (gammaSL 1 (b*c⁻¹) • I) (gammaSL 1 b • x) I]
    · change surfaceAddress d (projectPoint (d+1) y) = _
      rw [hw]
      change ((c⁻¹ : gamma 1) : Deck (d+1)) =
        ((b⁻¹ : gamma 1) : Deck (d+1)) * ((b*c⁻¹ : gamma 1) : Deck (d+1))
      rw [← QuotientGroup.mk_mul]; simp

end Cover

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.CoverLorentzInjectivity

/-!
# The metric on the congruence surfaces

The distance between two orbits is the smallest hyperbolic distance from a
representative to a translate of the other. Properness gives an attained minimum.
At large depth the quotient projection restricts to an isometric bijection from
each ball onto the ball with the same radius downstairs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set UpperHalfPlane
open scoped Pointwise MatrixGroups

/-- Points of the hyperbolic plane identified by the congruence group. -/
def planeRel (l : ℕ) : Setoid ℍ where
  r x y := ∃ u : gamma l, gammaSL l u • x = y
  iseqv := ⟨fun _ => ⟨1,by simp⟩,by
    rintro x _ ⟨u,rfl⟩
    exact ⟨u⁻¹,by rw [map_inv,inv_smul_smul]⟩,by
    rintro x _ _ ⟨u,rfl⟩ ⟨v,rfl⟩
    exact ⟨v*u,by rw [map_mul,mul_smul]⟩⟩

/-- The quotient surface at the given level. -/
def Surface (l : ℕ) := Quotient (planeRel l)

/-- The covering projection from the upper half-plane to its congruence quotient. -/
def projectPoint (l : ℕ) (z : ℍ) : Surface l := Quotient.mk (planeRel l) z

private theorem closest_exists (l : ℕ) (x y : ℍ) : ∃ g : gamma l, ∀ u : gamma l,
    dist x (gammaSL l g • y) ≤ dist x (gammaSL l u • y) := by
  classical
  have hf := finite_movers l (isCompact_singleton (x := y)) (ProperSpace.isCompact_closedBall x (dist x y))
  let s := hf.toFinset
  have hm (u : gamma l) : u ∈ s ↔ dist x (gammaSL l u • y) ≤ dist x y := by
    rw [hf.mem_toFinset]
    simp [movers,Metric.mem_closedBall,dist_comm x]
  have h1 := (hm 1).mpr (by simp)
  obtain ⟨g,hg,hmin⟩ := s.exists_min_image (fun u => dist x (gammaSL l u • y)) ⟨1,h1⟩
  refine ⟨g,fun u => ?_⟩
  by_cases hu : u ∈ s
  · exact hmin _ hu
  · exact ((hm _).mp hg).trans (le_of_not_ge (fun he => hu ((hm _).mpr he)))

/-- Minimum hyperbolic distance between two congruence orbits. -/
noncomputable def orbitDistance (l : ℕ) (x y : ℍ) :=
  dist x (gammaSL l (closest_exists l x y).choose • y)

/-- A translate attains the orbit distance. -/
theorem orbitDistance_attained (l : ℕ) (x y : ℍ) :
    ∃ u : gamma l, orbitDistance l x y = dist x (gammaSL l u • y) :=
  ⟨(closest_exists l x y).choose,rfl⟩

/-- Every representative distance bounds the quotient distance from above. -/
theorem orbitDistance_le (l : ℕ) (x y : ℍ) (u : gamma l) :
    orbitDistance l x y ≤ dist x (gammaSL l u • y) := (closest_exists l x y).choose_spec u

private theorem orbitDistance_le_reindex (l : ℕ) (x y : ℍ) (a b : gamma l) :
    orbitDistance l x y ≤ orbitDistance l (gammaSL l a • x) (gammaSL l b • y) := by
  obtain ⟨c,hc⟩ := orbitDistance_attained l (gammaSL l a • x) (gammaSL l b • y)
  rw [hc]
  have h := orbitDistance_le l x y (a⁻¹*c*b)
  simpa only [map_mul,map_inv,mul_smul, ← dist_smul (gammaSL l a) x
    ((gammaSL l a)⁻¹ • (gammaSL l c • (gammaSL l b • y))),smul_inv_smul] using h

private theorem orbitDistance_invariant {l : ℕ} {x x' y y' : ℍ}
    (hx : (planeRel l).r x x') (hy : (planeRel l).r y y') : orbitDistance l x y = orbitDistance l x' y' := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  apply le_antisymm (orbitDistance_le_reindex _ _ _ a b)
  simpa only [map_inv,inv_smul_smul] using
    orbitDistance_le_reindex l (gammaSL l a • x) (gammaSL l b • y) a⁻¹ b⁻¹

private theorem orbitDistance_comm_le (l : ℕ) (x y : ℍ) : orbitDistance l x y ≤ orbitDistance l y x := by
  obtain ⟨a,ha⟩ := orbitDistance_attained l y x
  rw [ha,dist_comm,← dist_smul ((gammaSL l a)⁻¹),inv_smul_smul]
  simpa only [map_inv] using orbitDistance_le l x y a⁻¹

private theorem orbitDistance_triangle (l : ℕ) (x y z : ℍ) :
    orbitDistance l x z ≤ orbitDistance l x y + orbitDistance l y z := by
  obtain ⟨a,ha⟩ := orbitDistance_attained l x y
  obtain ⟨b,hb⟩ := orbitDistance_attained l y z
  rw [ha,hb,← dist_smul (gammaSL l a) y (gammaSL l b • z)]
  calc
    _ ≤ dist x (gammaSL l (a*b) • z) := orbitDistance_le _ _ _ _
    _ ≤ _ := by rw [map_mul,mul_smul]; exact dist_triangle _ _ _

/-- The genuine quotient metric, using minimization over integral congruence translates. -/
noncomputable instance surfaceMetric (l : ℕ) : MetricSpace (Surface l) where
  dist x y := Quotient.liftOn₂ (s₁ := planeRel l) (s₂ := planeRel l) x y (orbitDistance l)
    (fun _ _ _ _ hx hy => orbitDistance_invariant hx hy)
  dist_self x := Quotient.inductionOn x fun z => by
    change orbitDistance l z z = 0
    exact le_antisymm (by simpa only [map_one,one_smul,dist_self] using orbitDistance_le l z z 1) dist_nonneg
  dist_comm x y := Quotient.inductionOn₂ x y fun a b =>
    le_antisymm (orbitDistance_comm_le l a b) (orbitDistance_comm_le l b a)
  dist_triangle x y z := Quotient.inductionOn₃ x y z (orbitDistance_triangle l)
  eq_of_dist_eq_zero := by
    rintro ⟨x⟩ ⟨y⟩ h
    obtain ⟨a,ha⟩ := orbitDistance_attained l x y
    have he : x = gammaSL l a • y := dist_eq_zero.mp (ha.symm.trans h)
    exact Quotient.sound ((planeRel l).symm ⟨a,he.symm⟩)

/-- The orbit projection contracts distances. -/
theorem dist_projectPoint_le (l : ℕ) (x y : ℍ) :
    dist (projectPoint l x) (projectPoint l y) ≤ dist x y := by
  change orbitDistance l x y ≤ dist x y
  simpa only [map_one,one_smul] using orbitDistance_le l x y 1

/-- Closed balls downstairs are exactly the images of the corresponding balls upstairs. -/
theorem project_closedBall (l : ℕ) (x : ℍ) (r : ℝ) :
    projectPoint l '' Metric.closedBall x r = Metric.closedBall (projectPoint l x) r := by
  ext y
  induction y using Quotient.inductionOn with
  | _ z =>
    constructor
    · rintro ⟨w,hw,he⟩
      change dist (projectPoint l z) (projectPoint l x) ≤ r
      change projectPoint l w = projectPoint l z at he
      rw [← he]
      exact (dist_projectPoint_le l w x).trans hw
    · intro hz
      obtain ⟨a,ha⟩ := orbitDistance_attained l x z
      refine ⟨gammaSL l a • z,?_,?_⟩
      · change dist (gammaSL l a • z) x ≤ r
        rw [dist_comm,← ha]
        change dist (projectPoint l x) (projectPoint l z) ≤ r
        rwa [dist_comm]
      · exact Quotient.sound ((planeRel l).symm ⟨a,rfl⟩)

/-- At each fixed radius, all sufficiently deep covering projections give isometric bijections
on all closed balls simultaneously. -/
theorem eventually_isometry_closedBall (r : ℝ) : ∃ l, ∀ d ≥ l, ∀ o : ℍ,
    Isometry (fun x : Metric.closedBall o r => projectPoint d x.val) ∧
      projectPoint d '' Metric.closedBall o r = Metric.closedBall (projectPoint d o) r := by
  obtain ⟨l,hl⟩ := eventually_ball_distances r
  refine ⟨l,fun d hd o => ⟨Isometry.of_dist_eq ?_,project_closedBall _ _ _⟩⟩
  intro x y
  obtain ⟨u,hu⟩ := orbitDistance_attained d x.val y.val
  change orbitDistance d x.val y.val = dist x.val y.val
  refine le_antisymm (dist_projectPoint_le _ _ _) ?_
  rw [hu]
  exact hl d hd o x.val y.val x.2 y.2 u

/-- The projection of the universal cover is continuous for the quotient metric. -/
theorem continuous_projectPoint (l : ℕ) : Continuous (projectPoint l) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa using dist_projectPoint_le l x y

/-- Each quotient surface is compact for its hyperbolic quotient metric. -/
noncomputable instance surfaceCompact (l : ℕ) : CompactSpace (Surface l) := by
  have he : projectPoint l '' dirichlet l = univ := by
    apply eq_univ_iff_forall.mpr
    rintro ⟨z⟩
    obtain ⟨u,hu⟩ := exists_mem_dirichlet l z
    exact ⟨gammaSL l u • z,hu,Quotient.sound ((planeRel l).symm ⟨u,rfl⟩)⟩
  exact ⟨he ▸ (dirichlet_compact l).image (continuous_projectPoint l)⟩

end Cover

end BorderVNP
end Computability
end OAI

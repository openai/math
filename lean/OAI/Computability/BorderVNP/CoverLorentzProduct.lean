import OAI.Computability.BorderVNP.CoverLorentzMotion
import OAI.Computability.BorderVNP.ShortenEpochProduct

/-!
# Placing wires in products of congruence surfaces

The host has the Riemannian ℓ² product metric, also for the quotient surfaces.
A collection of endpoint slots in a bounded ball admits a common local lift.
Different collections can use different lifts, even when two of their old sites
coincide in the quotient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open UpperHalfPlane BorderVNP.Cover.Frame BorderVNP.Epoch
open scoped ENNReal

variable {I : Type*} [Fintype I]

/-- The tiled product surface with the ℓ² metric of §6. -/
abbrev SurfaceHost (I : Type*) (l : ℕ) := PiLp 2 (fun _ : I => Surface l)

/-- Coordinatewise projection of the product universal cover. -/
def productProjection (l : ℕ) (x : HyperbolicHost I) : SurfaceHost I l :=
  WithLp.toLp 2 (fun i => projectPoint l (x i))

/-- Squared distances in the tiled host sum across the surface factors. -/
theorem surfaceHost_dist_sq {l : ℕ} (x y : SurfaceHost I l) :
    dist x y ^ 2 = ∑ i, dist (x i) (y i)^2 := by
  rw [PiLp.dist_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- Projection to the tiled product host cannot increase any wire length. -/
theorem productProjection_dist_le (l : ℕ) (x y : HyperbolicHost I) :
    dist (productProjection l x) (productProjection l y) ≤ dist x y := by
  rw [← sq_le_sq₀ dist_nonneg dist_nonneg,surfaceHost_dist_sq,host_dist_sq]
  exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ dist_nonneg (dist_projectPoint_le l (x i) (y i)) 2)

/-- Each quotient point admits a lift realizing exactly its distance to a fixed lifted center. -/
theorem productProjection_closest_lift {l : ℕ} (o : HyperbolicHost I) (x : SurfaceHost I l) :
    ∃ y : HyperbolicHost I, productProjection l y = x ∧ dist o y = dist (productProjection l o) x := by
  have hc (i : I) : ∃ p : ℍ, projectPoint l p = x i ∧ dist (o i) p = dist (projectPoint l (o i)) (x i) := by
    obtain ⟨q,hq⟩ : ∃ q : ℍ, projectPoint l q = x i := Quotient.exists_rep (x i)
    obtain ⟨u,hu⟩ := orbitDistance_attained l (o i) q
    refine ⟨gammaSL l u • q,(Quotient.sound ((planeRel l).symm ⟨u,rfl⟩)).trans hq,?_⟩
    rw [← hq]
    exact hu.symm
  choose p hp he using hc
  let y : HyperbolicHost I := WithLp.toLp 2 p
  refine ⟨y,PiLp.ext hp,?_⟩
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg,host_dist_sq,surfaceHost_dist_sq]
  exact Finset.sum_congr rfl (fun i _ => congrArg (·^2) (he i))

/-- The product projection eventually preserves distances throughout every fixed-radius ball. -/
theorem eventually_productProjection_isometry (r : ℝ) : ∃ l, ∀ d ≥ l, ∀ o : HyperbolicHost I,
    Isometry (fun z : Metric.closedBall o r => productProjection d z.val) := by
  obtain ⟨l,hl⟩ := eventually_isometry_closedBall r
  refine ⟨l,?_⟩
  intro d hd o
  apply Isometry.of_dist_eq
  intro x y
  change dist (productProjection d x.val) (productProjection d y.val) = dist x.val y.val
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg,surfaceHost_dist_sq,host_dist_sq]
  refine Finset.sum_congr rfl (fun i _ => congrArg (·^2) ?_)
  have hx : x.val i ∈ Metric.closedBall (o i) r := (PiLp.dist_apply_le x.val o i).trans x.2
  have hy : y.val i ∈ Metric.closedBall (o i) r := (PiLp.dist_apply_le y.val o i).trans y.2
  exact ((hl d hd (o i)).1.dist_eq ⟨_,hx⟩ ⟨_,hy⟩)

/-- A whole seed's endpoint slots in one ball have simultaneous lifts preserving all pair
distances. The lift is local to that seed. -/
theorem eventually_lift_slots (r : ℝ) : ∃ l, ∀ d ≥ l, ∀ (o : HyperbolicHost I)
    {P : Type*} (x : P → SurfaceHost I d),
    (∀ i, dist (x i) (productProjection d o) ≤ r) →
    ∃ y : P → HyperbolicHost I, (∀ i, productProjection d (y i) = x i) ∧
      (∀ i, dist (y i) o = dist (x i) (productProjection d o)) ∧
      ∀ i j, dist (y i) (y j) = dist (x i) (x j) := by
  obtain ⟨l,hl⟩ := eventually_productProjection_isometry (I := I) r
  refine ⟨l,?_⟩
  intro d hd o P x hx
  choose y hp he using (fun i => productProjection_closest_lift o (x i))
  have hball (i : P) : y i ∈ Metric.closedBall o r := by
    change dist (y i) o ≤ r
    rw [dist_comm,he,dist_comm]
    exact hx i
  refine ⟨y,hp,fun i => by simpa only [dist_comm (y i) o,dist_comm (x i) (productProjection d o)] using he i,?_⟩
  intro i j
  rw [← hp i,← hp j]
  exact ((hl d hd o).dist_eq ⟨y i,hball i⟩ ⟨y j,hball j⟩).symm

/-- Product motion with a prescribed permutation of the surface factors. -/
noncomputable def productMotion {a : ℕ} (d : ℕ) (e : I ≃ I) {g : I → SL}
    (hg : ∀ i, Clears (g i) a) (x : SurfaceHost I (d+2*a)) : SurfaceHost I d :=
  WithLp.toLp 2 (fun i => surfaceMotion (hg i) d (x (e i)))

/-- Whole-network product motion is globally distance-nonincreasing, including factor permutations. -/
theorem productMotion_dist_le {a : ℕ} (d : ℕ) (e : I ≃ I) {g : I → SL} (hg : ∀ i, Clears (g i) a)
    (x y : SurfaceHost I (d+2*a)) : dist (productMotion d e hg x) (productMotion d e hg y) ≤ dist x y := by
  rw [← sq_le_sq₀ dist_nonneg dist_nonneg,surfaceHost_dist_sq,surfaceHost_dist_sq]
  calc
    _ ≤ ∑ i, dist (x (e i)) (y (e i))^2 := Finset.sum_le_sum (fun i _ =>
      pow_le_pow_left₀ dist_nonneg (surfaceMotion_dist_le (hg i) d _ _) 2)
    _ = _ := e.sum_comp (fun j => dist (x j) (y j)^2)

/-- Whole-network motions preserve distances on every prescribed ball at sufficiently large
levels, uniformly over motions and permutations. -/
theorem eventually_productMotion_isometry (r : ℝ) : ∃ l, ∀ d ≥ l, ∀ {a : ℕ} (e : I ≃ I) {g : I → SL}
    (hg : ∀ i, Clears (g i) a) (o : SurfaceHost I (d+2*a)),
    Isometry (fun z : Metric.closedBall o r => productMotion d e hg z.val) := by
  obtain ⟨l,hl⟩ := eventually_surfaceMotion_isometry r
  refine ⟨l,?_⟩
  intro d hd a e g hg o
  apply Isometry.of_dist_eq
  intro x y
  change dist (productMotion d e hg x.val) (productMotion d e hg y.val) = dist x.val y.val
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg,surfaceHost_dist_sq,surfaceHost_dist_sq]
  rw [← e.sum_comp (fun j => dist (x.val j) (y.val j)^2)]
  refine Finset.sum_congr rfl (fun i _ => congrArg (·^2) ?_)
  have hx : x.val (e i) ∈ Metric.closedBall (o (e i)) r := (PiLp.dist_apply_le x.val o (e i)).trans x.2
  have hy : y.val (e i) ∈ Metric.closedBall (o (e i)) r := (PiLp.dist_apply_le y.val o (e i)).trans y.2
  exact (hl d hd (hg i) (o (e i))).dist_eq ⟨_,hx⟩ ⟨_,hy⟩

end Cover

end BorderVNP
end Computability
end OAI

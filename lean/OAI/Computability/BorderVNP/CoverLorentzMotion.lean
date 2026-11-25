import OAI.Computability.BorderVNP.CoverLorentzSurface
import OAI.Computability.BorderVNP.CoverHeckeDenominators

/-!
# The induced motion on quotient surfaces

A norm-one rational quaternion whose denominator clears at depth `a` acts by an
isometry upstairs. Its conjugation sends the input level group into the output
level group with depth loss `2a`. The induced surjection is distance-nonincreasing
and maps every sufficiently small ball isometrically onto the corresponding ball.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set UpperHalfPlane BorderVNP.Cover.Frame
open scoped MatrixGroups

/-- The surface map induced by a motion with denominator cleared by `7^a`. -/
noncomputable def surfaceMotion {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    Surface (d+2*a) → Surface d :=
  Quotient.map (g • ·) (by
    intro x y h
    obtain ⟨u,rfl⟩ := h
    obtain ⟨v,hv⟩ := conjugate_lattice hg d (show gammaSL (d+2*a) u ∈ lattice (d+2*a) from ⟨u,rfl⟩)
    exact ⟨v,by rw [hv,mul_smul,mul_smul,inv_smul_smul]⟩)

/-- Motion of a represented point is the projected isometric translate of its lift. -/
theorem surfaceMotion_project {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) (x : ℍ) :
    surfaceMotion hg d (projectPoint (d+2*a) x) = projectPoint d (g • x) := rfl

/-- Every point on the shallower surface has a preimage. -/
theorem surfaceMotion_surjective {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    Function.Surjective (surfaceMotion hg d) := by
  rintro ⟨x⟩
  exact ⟨projectPoint _ (g⁻¹ • x),by rw [surfaceMotion_project,smul_inv_smul]; rfl⟩

/-- Conjugating a closest representative gives a distance bound on the output surface. -/
theorem surfaceMotion_dist_le {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ)
    (x y : Surface (d+2*a)) : dist (surfaceMotion hg d x) (surfaceMotion hg d y) ≤ dist x y := by
  induction x,y using Quotient.inductionOn₂ with
  | _ x y =>
    change orbitDistance d (g • x) (g • y) ≤ orbitDistance (d+2*a) x y
    obtain ⟨u,hu⟩ := orbitDistance_attained (d+2*a) x y
    obtain ⟨v,hv⟩ := conjugate_lattice hg d (show gammaSL (d+2*a) u ∈ lattice (d+2*a) from ⟨u,rfl⟩)
    have h := orbitDistance_le d (g • x) (g • y) v
    rwa [hv,mul_smul,mul_smul,inv_smul_smul,dist_smul,← hu] at h

/-- The image of a closed ball is the closed ball of the same radius. -/
theorem surfaceMotion_closedBall {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ)
    (x : Surface (d+2*a)) (r : ℝ) :
    surfaceMotion hg d '' Metric.closedBall x r = Metric.closedBall (surfaceMotion hg d x) r := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change surfaceMotion hg d '' Metric.closedBall (projectPoint _ x) r =
      Metric.closedBall (surfaceMotion hg d (projectPoint _ x)) r
    rw [surfaceMotion_project,← project_closedBall,← project_closedBall, image_image]
    ext y
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨g • w,by change dist (g • w) (g • x) ≤ r; rwa [dist_smul],rfl⟩
    · rintro ⟨w,hw,rfl⟩
      refine ⟨g⁻¹ • w,?_,?_⟩
      · change dist (g⁻¹ • w) x ≤ r
        rw [← dist_smul g,smul_inv_smul]
        exact hw
      · change surfaceMotion hg d (projectPoint _ (g⁻¹ • w)) = projectPoint _ w
        rw [surfaceMotion_project,smul_inv_smul]

/-- At every prescribed radius, the quotient motion is isometric on each ball at
all sufficiently deep output levels. The threshold is independent of its denominator. -/
theorem eventually_surfaceMotion_isometry (r : ℝ) : ∃ l, ∀ d ≥ l,
    ∀ {g : SL} {a : ℕ} (hg : Clears g a) (o : Surface (d+2*a)),
      Isometry (fun x : Metric.closedBall o r => surfaceMotion hg d x.val) := by
  obtain ⟨l,hl⟩ := eventually_isometry_closedBall r
  refine ⟨l,?_⟩
  intro d hd g a hg o
  induction o using Quotient.inductionOn with
  | _ o =>
    refine Isometry.of_dist_eq ?_
    intro x y
    have hin := (hl (d+2*a) (by omega) o).1
    have hout := (hl d hd (g • o)).1
    have lift (v : Metric.closedBall (projectPoint (d+2*a) o) r) :
        ∃ w ∈ Metric.closedBall o r, projectPoint (d+2*a) w = v.val :=
      (project_closedBall _ o r).ge v.2
    obtain ⟨p,hp,he⟩ := lift x
    obtain ⟨q,hq,hf⟩ := lift y
    change dist (surfaceMotion hg d x.val) (surfaceMotion hg d y.val) = dist x.val y.val
    rw [← he,← hf,surfaceMotion_project,surfaceMotion_project]
    have hp' : g • p ∈ Metric.closedBall (g • o) r := by
      change dist (g • p) (g • o) ≤ r; rwa [dist_smul]
    have hq' : g • q ∈ Metric.closedBall (g • o) r := by
      change dist (g • q) (g • o) ≤ r; rwa [dist_smul]
    exact (hout.dist_eq ⟨_,hp'⟩ ⟨_,hq'⟩).trans ((dist_smul g p q).trans (hin.dist_eq ⟨p,hp⟩ ⟨q,hq⟩).symm)

end Cover

end BorderVNP
end Computability
end OAI

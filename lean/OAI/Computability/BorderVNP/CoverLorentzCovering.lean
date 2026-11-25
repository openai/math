import OAI.Computability.BorderVNP.CoverLorentzMotion
import Mathlib.Topology.Covering.Basic

/-!
# The covering property at every positive output level

A fixed level has a strictly positive local injectivity radius at each point:
only finitely many units move that point a distance at most one, and none of the
nonidentity units fix it. The surjective quaternion motion is locally isometric,
open, and (between compact surfaces) a topological covering map.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Set Matrix UpperHalfPlane Topology BorderVNP.Cover.Frame

private theorem positive_displacement (l : ℕ) (o : ℍ) :
    ∃ t : ℝ, 0 < t ∧ ∀ u : gamma (l+1), u ≠ 1 → t ≤ dist (gammaSL (l+1) u • o) o := by
  classical
  let f (u : gamma (l+1)) := dist (gammaSL (l+1) u • o) o
  have hf := finite_movers (l+1) (isCompact_singleton (x := o)) (ProperSpace.isCompact_closedBall o 1)
  let s := hf.toFinset.erase 1
  let t := insert (1 : ℝ) (s.image f)
  have h1 : (1 : ℝ) ∈ t := Finset.mem_insert_self _ _
  have hne : t.Nonempty := ⟨1,h1⟩
  have hpos (y : ℝ) (hy : y ∈ t) : 0 < y := by
    rcases Finset.mem_insert.mp hy with rfl|hs
    · norm_num
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
      exact dist_pos.mpr (fun h => (Finset.mem_erase.mp hu).1 (eq_one_of_fix u o h))
  refine ⟨t.min' hne,hpos _ (t.min'_mem hne),?_⟩
  intro u hu
  by_cases h : f u ≤ 1
  · have hmem : u ∈ s := Finset.mem_erase.mpr ⟨hu,hf.mem_toFinset.mpr ⟨gammaSL (l+1) u • o,
        ⟨o,rfl,rfl⟩,h⟩⟩
    exact t.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hmem))
  · exact (t.min'_le _ h1).trans (le_of_not_ge h)

/-- Each point of each positive level has a ball lifted isometrically from the plane. -/
theorem exists_isometry_projectPoint (l : ℕ) (o : ℍ) : ∃ r : ℝ, 0 < r ∧
    Isometry (fun z : Metric.closedBall o r => projectPoint (l+1) z.val) := by
  obtain ⟨t,ht,hm⟩ := positive_displacement l o
  refine ⟨t/5,by positivity,Isometry.of_dist_eq ?_⟩
  intro x y
  change orbitDistance (l+1) x.val y.val = dist x.val y.val
  refine le_antisymm (dist_projectPoint_le _ _ _) ?_
  obtain ⟨u,hu⟩ := orbitDistance_attained (l+1) x.val y.val
  rw [hu]
  by_cases h : u = 1
  · simp [h]
  · by_contra! hc
    have hx : dist x.val o ≤ t/5 := x.2
    have hy : dist y.val o ≤ t/5 := y.2
    have hxy := dist_triangle x.val o y.val
    rw [dist_comm o y.val] at hxy
    have hmove := dist_triangle (gammaSL (l+1) u • o) (gammaSL (l+1) u • y.val) o
    rw [dist_smul,dist_comm o y.val] at hmove
    have hshort := dist_triangle (gammaSL (l+1) u • y.val) x.val o
    rw [dist_comm (gammaSL (l+1) u • y.val) x.val] at hshort
    linarith [hm _ h]

/-- The induced motion is a local isometry at every positive output level. -/
theorem surfaceMotion_local_isometry {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ)
    (o : Surface (d+1+2*a)) : ∃ r : ℝ, 0 < r ∧
    Isometry (fun z : Metric.closedBall o r => surfaceMotion hg (d+1) z.val) := by
  induction o using Quotient.inductionOn with
  | _ o =>
    obtain ⟨r,hr,hiso⟩ := exists_isometry_projectPoint d (g • o)
    refine ⟨r,hr,Isometry.of_dist_eq ?_⟩
    intro x y
    obtain ⟨p,hp,he⟩ := (project_closedBall _ o r).ge x.property
    obtain ⟨q,hq,hf⟩ := (project_closedBall _ o r).ge y.property
    change dist (surfaceMotion hg (d+1) x.val) (surfaceMotion hg (d+1) y.val) = dist x.val y.val
    refine le_antisymm (surfaceMotion_dist_le _ _ _ _) ?_
    rw [← he,← hf,surfaceMotion_project,surfaceMotion_project]
    have hp' : g • p ∈ Metric.closedBall (g • o) r := by change dist (g • p) (g • o) ≤ r; rwa [dist_smul]
    have hq' : g • q ∈ Metric.closedBall (g • o) r := by change dist (g • q) (g • o) ≤ r; rwa [dist_smul]
    exact (dist_projectPoint_le _ _ _).trans_eq ((dist_smul g p q).symm.trans
      (hiso.dist_eq ⟨_,hp'⟩ ⟨_,hq'⟩).symm)

/-- The induced quotient motion is open at every level. -/
theorem surfaceMotion_open {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    IsOpenMap (surfaceMotion hg d) := by
  intro s hs
  apply Metric.isOpen_iff.mpr
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨r,hr,hsr⟩ := Metric.isOpen_iff.mp hs x hx
  refine ⟨r/2,half_pos hr,?_⟩
  intro z hz
  have hm := (surfaceMotion_closedBall hg d x (r/2)).ge (Metric.ball_subset_closedBall hz)
  obtain ⟨w,hw,rfl⟩ := hm
  exact ⟨w,hsr ((Metric.closedBall_subset_ball (half_lt_self hr)) hw),rfl⟩

/-- The local isometries define an actual covering map of compact surfaces. -/
theorem surfaceMotion_covering {g : SL} {a : ℕ} (hg : Clears g a) (d : ℕ) :
    IsCoveringMap (surfaceMotion hg (d+1)) := by
  have hc : Continuous (surfaceMotion hg (d+1)) := by
    apply LipschitzWith.continuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    simpa using surfaceMotion_dist_le hg (d+1)
  apply isLocalHomeomorph_iff_isCoveringMap.mp
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨r,hr,hi⟩ := surfaceMotion_local_isometry hg d x
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds x hr, .of_continuous_injective_isOpenMap
    (hc.comp continuous_subtype_val) ?_ ((surfaceMotion_open hg (d+1)).domRestrict Metric.isOpen_ball)⟩
  intro u v he
  have h := hi.injective (a₁ := ⟨u.val,Metric.ball_subset_closedBall u.2⟩)
    (a₂ := ⟨v.val,Metric.ball_subset_closedBall v.2⟩) he
  exact Subtype.ext (congrArg (fun w : Metric.closedBall x r => w.val) h)

end Cover

end BorderVNP
end Computability
end OAI

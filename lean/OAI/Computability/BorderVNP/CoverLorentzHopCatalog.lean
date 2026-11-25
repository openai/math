import OAI.Computability.BorderVNP.CoverLorentzSitePack

/-!
# Oriented segment templates and the transition back to site packs

The subdivision geodesics have strictly positive, level-independent lengths.
Their finitely many endpoint pairs admit the normalized midpoint presentation
used by the frame motions. When an epoch rounds its short segments back to
sites, the resulting pack carries an allowed route for every nonlocal charged
wire, ready for the next epoch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set UpperHalfPlane BorderVNP.Epoch BorderVNP.Shortening
open scoped Classical

variable {I : Type*} [Fintype I] {L h : ℝ}

/-- The geometric midpoint and oriented unit tangent template of one catalog segment. -/
structure FramedHop (t : Hop I L h) where
  /-- Center in the lifted host. -/
  center : HyperbolicHost I
  /-- Unit product direction, including possible zero component speeds. -/
  direction : PiLp 2 (fun _ : I => ℂ)
  /-- Unit speed on the full product. -/
  unit : ‖direction‖ = 1
  /-- The catalog's first endpoint. -/
  first : shiftTo center (productLine direction (-(hopLength h t.1/2))) = hopPosition t 0
  /-- The catalog's second endpoint. -/
  last : shiftTo center (productLine direction (hopLength h t.1/2)) = hopPosition t 1

/-- Fix an oriented midpoint line for each of the finitely many strictly positive catalog hops. -/
noncomputable def framedHop (hh : 0 < h) (t : Hop I L h) : FramedHop t := by
  apply Classical.choice
  have hp : 0 < dist (hopPosition t 0) (hopPosition t 1) :=
    (dist_hopPosition hh t).symm ▸ (hopLength_bounds hh t.1).1
  obtain ⟨c,v,hv,ha,hb⟩ := exists_product_midpoint_line _ _ (dist_pos.mp hp)
  rw [dist_hopPosition hh t] at ha hb
  exact ⟨⟨c,v,hv,ha,hb⟩⟩

/-- The oriented template gives a fixed integral carry for the tile of its center. -/
noncomputable def centerCarry (hh : 0 < h) (t : Hop I L h) : I → gamma 1 :=
  fun i => (Frame.toBaseTile ((framedHop hh t).center i))⁻¹

/-- The tile in which an oriented midpoint is binned is a table offset of its start tile. -/
theorem centerAddress (hh : 0 < h) (t : Hop I L h) (d : ℕ) (a : I → gamma 1) :
    productAddress d (productProjection (d+1) (translatePoint a (framedHop hh t).center)) =
      reduceMove d a * reduceMove d (centerCarry hh t) := productAddress_translate _ _ _

/-- Along the true fixed geodesic, all points of a catalog hop stay within the overall
site displacement budget. -/
theorem hop_in_ball (hh : 0 < h) (t : Hop I L h) {f : ℝ} (hf : f ∈ Icc 0 1) :
    hopPosition t f ∈ Metric.closedBall (productOrigin I) L := by
  have hn : (hopCount L h : ℝ) ≠ 0 := by simp [hopCount]; positivity
  have hle : (t.2.val : ℝ)+1 ≤ hopCount L h := by exact_mod_cast t.2.isLt
  have hp := (hopLength_bounds hh t.1).1
  rw [Metric.mem_closedBall,hopPosition,← (moveLine t.1).start,(moveLine t.1).isometry.dist_eq,Real.dist_eq,sub_zero]
  rw [abs_of_nonneg (mul_nonneg (add_nonneg (Nat.cast_nonneg _) hf.1) hp.le)]
  calc
    _ ≤ (hopCount L h : ℝ)*hopLength h t.1 := mul_le_mul_of_nonneg_right (by linarith [hf.2]) hp.le
    _ = moveLength t.1.val := by dsimp [hopLength]; field_simp
    _ ≤ L := (mem_allowedMoves.mp t.1.2).2

/-- Beyond a fixed level the actual projected, translated wire has precisely its catalogued
length at each subdivision hop. -/
theorem eventually_hop_length (hh : 0 < h) : ∃ l, ∀ d ≥ l, ∀ (a : I → gamma 1) (t : Hop I L h),
    dist (productProjection d (translatePoint a (hopPosition t 0)))
      (productProjection d (translatePoint a (hopPosition t 1))) = hopLength h t.1 := by
  obtain ⟨l,hl⟩ := eventually_productProjection_isometry (I := I) L
  refine ⟨l,?_⟩
  intro d hd a t
  let o := translatePoint a (productOrigin I)
  have hin (f : ℝ) (hf : f ∈ Icc 0 1) : translatePoint a (hopPosition t f) ∈ Metric.closedBall o L :=
    ((translatePoint_isometry a).dist_eq _ _).le.trans (hop_in_ball hh t hf)
  exact ((hl d hd o).dist_eq ⟨_,hin 0 (by simp)⟩ ⟨_,hin 1 (by simp)⟩).trans
    (((translatePoint_isometry a).dist_eq _ _).trans (dist_hopPosition hh t))

/-- All short endpoint pairs round to a pack with genuine allowed site moves, uniformly over
the tensor tables, the nonlocal subset, and the depth of the cover. -/
theorem rounded_site_routes (h : ℝ) : ∃ L : ℝ, 0 < L ∧
    (∀ s : I → gamma 1, s ≠ 1 → (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) → s ∈ allowedMoves I L) ∧
    ∀ {D d : ℕ} {P R : Type*} {bits : P → ℕ} (p : Pack D P bits R)
      (atPoint : p.layout.Site → SurfaceHost I (d+1)) (charged : p.layout.Edge → Bool),
    (∀ e, charged e → dist (atPoint (p.layout.src e)) (atPoint (p.layout.dst e)) ≤ h) →
    ∃ routes : SiteRoutes p I d L, (∀ v, reduceMove d (routes.origin v) = productAddress d (atPoint v)) ∧
      (∀ e, routes.active e ↔ charged e ∧
        productAddress d (atPoint (p.layout.src e)) ≠ productAddress d (atPoint (p.layout.dst e))) ∧
      ∀ v i, routes.site v i = roundedSite d (atPoint v i) := by
  obtain ⟨L,hL,hgen,hpair⟩ := exists_move_budget (I := I) h
  refine ⟨L,hL,hgen,?_⟩
  intro D d P R bits p pos charged hc
  let a (v : p.layout.Site) (i : I) : gamma 1 := (productAddress d (pos v) i).out
  have ha (v : p.layout.Site) : reduceMove d (a v) = productAddress d (pos v) :=
    funext (fun i => Quotient.out_eq _)
  let active (e : p.layout.Edge) := decide (charged e ∧
    productAddress d (pos (p.layout.src e)) ≠ productAddress d (pos (p.layout.dst e)))
  have hs (e : p.layout.Edge) (he : active e) : ∃ s ∈ allowedMoves I L,
      productAddress d (pos (p.layout.dst e)) = productAddress d (pos (p.layout.src e)) * reduceMove d s := by
    have he' := of_decide_eq_true he
    exact hpair d _ _ (hc e he'.1) he'.2
  let routes : SiteRoutes p I d L :=
    { origin := a, active := active, step := fun e he => ⟨(hs e he).choose,(hs e he).choose_spec.1⟩
      aligned := fun e he => by rw [ha,ha]; exact (hs e he).choose_spec.2 }
  refine ⟨routes,ha,fun e => by simp [routes,active],?_⟩
  intro v i
  exact congrArg (deckSite d) (congrFun (ha v) i)

end Cover

end BorderVNP
end Computability
end OAI

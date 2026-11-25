import OAI.Computability.BorderVNP.CoverLorentzMoves
import OAI.Computability.BorderVNP.ShortenEpochSegments

/-!
# Fixed geodesic subdivision of the allowed site moves

For each allowed integral displacement choose one oriented unit-speed geodesic.
One integer number of hops works for all catalog entries. Translation changes
only the input tile address: the endpoint and midpoint carries are fixed table
entries of the move and hop.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Set Matrix UpperHalfPlane BorderVNP.Epoch

variable {I : Type*} [Fintype I]

/-- An oriented unit-speed realization of one integral site move. -/
structure MoveLine (s : I → gamma 1) where
  /-- Unit-speed geodesic starting at the product site. -/
  atTime : ℝ → HyperbolicHost I
  /-- Distance along the line is elapsed time. -/
  isometry : Isometry atTime
  /-- The first endpoint is the distinguished site. -/
  start : atTime 0 = productOrigin I
  /-- The final endpoint is the site reached by the given move. -/
  stop : atTime (moveLength s) = translatePoint s (productOrigin I)

/-- A fixed, level-independent geodesic for each positive allowed displacement. -/
noncomputable def moveLine {L : ℝ} (s : allowedMoves I L) : MoveLine s.val := by
  apply Classical.choice
  have hp := moveLength_pos.mpr (mem_allowedMoves.mp s.2).1
  obtain ⟨c,v,hv,ha,hb⟩ := exists_product_midpoint_line (productOrigin I)
    (translatePoint s.val (productOrigin I)) (dist_pos.mp hp)
  refine ⟨⟨fun t => shiftTo c (productLine v (t - moveLength s.val/2)),?_,?_,?_⟩⟩
  · apply Isometry.of_dist_eq
    intro t u
    rw [(shiftTo_isometry c).dist_eq,dist_productLine,hv,mul_one,Real.dist_eq]
    congr 1
    ring
  · simpa only [zero_sub,moveLength] using ha
  · rw [show moveLength s.val - moveLength s.val/2 = moveLength s.val/2 by ring]
    exact hb

/-- One fixed subdivision count suffices for the entire allowed-move catalog. -/
noncomputable def hopCount (L h : ℝ) : ℕ := ⌈L/h⌉₊ + 1

/-- A table index for one geometric segment in an allowed move. -/
abbrev Hop (I : Type*) [Fintype I] (L h : ℝ) := (allowedMoves I L) × Fin (hopCount L h)

/-- The common length of the pieces of a given integral move. -/
noncomputable def hopLength {L : ℝ} (h : ℝ) (s : allowedMoves I L) : ℝ :=
  moveLength s.val / hopCount L h

/-- Each catalogued subdivision piece has strictly positive length bounded by the cut scale. -/
theorem hopLength_bounds {L h : ℝ} (hh : 0 < h) (s : allowedMoves I L) : 0 < hopLength h s ∧ hopLength h s ≤ h := by
  have hn : 0 < (hopCount L h : ℝ) := by simp [hopCount]; positivity
  have hl := mem_allowedMoves.mp s.2
  refine ⟨div_pos (moveLength_pos.mpr hl.1) hn, (div_le_iff₀ hn).mpr ?_⟩
  have hb : L/h ≤ (hopCount L h : ℝ) := (Nat.le_ceil _).trans (by simp [hopCount])
  exact hl.2.trans ((div_le_iff₀ hh).mp hb |>.trans_eq (mul_comm _ _))

/-- Position at fraction `f` of a particular catalog hop: `f=0,1/2,1` select its start, midpoint,
and end. -/
noncomputable def hopPosition {L h : ℝ} (t : Hop I L h) (f : ℝ) : HyperbolicHost I :=
  (moveLine t.1).atTime (((t.2.val : ℝ)+f)*hopLength h t.1)

/-- Actual distance between the endpoints of each fixed subdivision pattern. -/
theorem dist_hopPosition {L h : ℝ} (hh : 0 < h) (t : Hop I L h) :
    dist (hopPosition t 0) (hopPosition t 1) = hopLength h t.1 := by
  rw [hopPosition,hopPosition,(moveLine t.1).isometry.dist_eq,Real.dist_eq]
  rw [show ((t.2.val:ℝ)+0)*hopLength h t.1 - ((t.2.val:ℝ)+1)*hopLength h t.1 = -hopLength h t.1 by ring,
    abs_neg,abs_of_nonneg (hopLength_bounds hh t.1).1.le]

/-- Adjacent hops in the catalog have exactly the same joining endpoint. -/
theorem hopPosition_next {L h : ℝ} (s : allowedMoves I L) (i j : Fin (hopCount L h))
    (hj : i.val+1 = j.val) : hopPosition (s,i) 1 = hopPosition (s,j) 0 := by
  simp only [hopPosition,add_zero]
  exact congrArg (fun n : ℝ => (moveLine s).atTime (n*hopLength h s)) (by exact_mod_cast hj)

/-- The first hop starts at the distinguished site. -/
theorem hopPosition_first {L h : ℝ} (s : allowedMoves I L) (i : Fin (hopCount L h))
    (hi : i.val = 0) : hopPosition (s,i) 0 = productOrigin I := by
  simp only [hopPosition,hi,Nat.cast_zero,zero_add,zero_mul,(moveLine s).start]

/-- The last hop ends at the site of the prescribed move. -/
theorem hopPosition_last {L h : ℝ} (s : allowedMoves I L) (i : Fin (hopCount L h))
    (hi : i.val+1 = hopCount L h) : hopPosition (s,i) 1 = translatePoint s.val (productOrigin I) := by
  have hn : (hopCount L h : ℝ) ≠ 0 := by simp [hopCount]; positivity
  have he : (i.val:ℝ)+1 = hopCount L h := by exact_mod_cast hi
  simp only [hopPosition,he,hopLength,mul_div_cancel₀ _ hn,(moveLine s).stop]

omit [Fintype I] in
/-- Translating an endpoint from a template changes the tile name by multiplication with the
fixed carry. This formula works also for seam points. -/
theorem productAddress_translate (d : ℕ) (a : I → gamma 1) (z : HyperbolicHost I) :
    productAddress d (productProjection (d+1) (translatePoint a z)) =
      reduceMove d a * productAddress d (productProjection (d+1) z) := by
  funext i
  change (↑(Frame.toBaseTile (gammaSL 1 (a i) • z i))⁻¹ : Deck (d+1)) =
    (↑(a i) : Deck (d+1)) * (↑(Frame.toBaseTile (z i))⁻¹ : Deck (d+1))
  rw [Frame.toBaseTile_smul,_root_.mul_inv_rev,inv_inv,QuotientGroup.mk_mul]

/-- A level-independent integral carry from the start address to a slot of a catalogued hop. -/
noncomputable def hopCarry {L h : ℝ} (t : Hop I L h) (f : ℝ) : I → gamma 1 :=
  fun i => (Frame.toBaseTile ((hopPosition t f) i))⁻¹

/-- The finite subdivision table computes the actual quotient tile of each segment endpoint or
midpoint by a single right multiplication. -/
theorem hopAddress {L h : ℝ} (t : Hop I L h) (f : ℝ) (d : ℕ) (a : I → gamma 1) :
    productAddress d (productProjection (d+1) (translatePoint a (hopPosition t f))) =
      reduceMove d a * reduceMove d (hopCarry t f) := productAddress_translate _ _ _

/-- The sum of the projected hop lengths is at most the initial site-wire length upstairs. -/
theorem sum_projected_hops_le {L h : ℝ} (hh : 0 < h) (s : allowedMoves I L) (d : ℕ) (a : I → gamma 1) :
    ∑ j : Fin (hopCount L h), dist (productProjection d (translatePoint a (hopPosition (s,j) 0)))
      (productProjection d (translatePoint a (hopPosition (s,j) 1))) ≤ moveLength s.val := by
  have hn : (hopCount L h : ℝ) ≠ 0 := by simp [hopCount]; positivity
  calc
    _ ≤ ∑ _j : Fin (hopCount L h), hopLength h s := by
      apply Finset.sum_le_sum
      intro j _
      exact (productProjection_dist_le _ _ _).trans_eq (((translatePoint_isometry a).dist_eq _ _).trans
        (dist_hopPosition hh (s,j)))
    _ = _ := by simp [hopLength]; field_simp

/-- Subdivision gives the initial total charged-length estimate `W ≤ L B` for arbitrary wire
widths and input sites. -/
theorem initial_length_le {L h : ℝ} (hh : 0 < h) {E : Type*} [Fintype E] (d : ℕ)
    (a : E → I → gamma 1) (s : E → allowedMoves I L) (width : E → ℕ) :
    ∑ e, (width e : ℝ) * ∑ j : Fin (hopCount L h),
      dist (productProjection d (translatePoint (a e) (hopPosition (s e,j) 0)))
        (productProjection d (translatePoint (a e) (hopPosition (s e,j) 1))) ≤ L * ∑ e, width e := by
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  rw [mul_comm L]
  exact mul_le_mul_of_nonneg_left ((sum_projected_hops_le hh (s e) d (a e)).trans
    (mem_allowedMoves.mp (s e).2).2) (Nat.cast_nonneg _)

end Cover

end BorderVNP
end Computability
end OAI

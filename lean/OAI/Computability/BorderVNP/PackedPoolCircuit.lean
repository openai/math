import OAI.Computability.BorderVNP.PackedDivision
import OAI.Computability.BorderVNP.PackedWordCircuit
import OAI.Computability.BorderVNP.ShortenSeedDescriptor

/-! # Computing simultaneous seed pool sizes

The incoming widths of the permuted direction bins determine the number of whole crossing
blocks available at a seed. This circuit computes the minimum, integer quotient and common
width on the same binary representation as the sparse histogram and clipping passes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PoolCircuit

open VPVNP.VerifierNetwork ParseBatchSort Word Shortening.SeedIntervals
open scoped Classical

private def minimumExpr {D : ℕ} [NeZero D] : List (Fin D) → WidthExpr (Fin D)
  | [] => .field 0
  | i :: rest => .binary .minimum (.field i) (minimumExpr rest)

private theorem minimum_lower {D : ℕ} [NeZero D] (x : Fin D → ℕ) (a : ℕ)
    (h : ∀ i, a ≤ x i) (is : List (Fin D)) : a ≤ (minimumExpr is).eval x := by
  induction is with
  | nil => exact h 0
  | cons i is ih => exact le_min (h i) ih

private theorem minimum_upper {D : ℕ} [NeZero D] (x : Fin D → ℕ) {i : Fin D}
    {is : List (Fin D)} (h : i ∈ is) : (minimumExpr is).eval x ≤ x i := by
  induction is with
  | nil => simp at h
  | cons j is ih =>
    rcases List.mem_cons.mp h with rfl | hi
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hi)

private theorem least_le {D : ℕ} [NeZero D] (x : Fin D → ℕ) (i : Fin D) :
    Epoch.leastCount x ≤ x i :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem x (Finset.mem_univ i))

private theorem least_attained {D : ℕ} [NeZero D] (x : Fin D → ℕ) :
    ∃ i, x i = Epoch.leastCount x := by
  classical
  obtain ⟨i, _, h⟩ := Finset.mem_image.mp
    (Finset.min'_mem _ (Finset.univ_nonempty.image x))
  exact ⟨i,h⟩

private theorem minimum_eq {D : ℕ} [NeZero D] (x : Fin D → ℕ) :
    (minimumExpr (List.finRange D)).eval x = Epoch.leastCount x := by
  obtain ⟨i,hi⟩ := least_attained x
  exact le_antisymm (hi ▸ minimum_upper x (List.mem_finRange i))
    (minimum_lower x _ (least_le x) _)

private theorem least_div {D : ℕ} [NeZero D] (x : Fin D → ℕ) (k : ℕ) :
    Epoch.leastCount (fun i => x i / k) = Epoch.leastCount x / k := by
  obtain ⟨i,hi⟩ := least_attained x
  obtain ⟨j,hj⟩ := least_attained (fun i => x i / k)
  exact le_antisymm (by simpa only [hi] using least_le (fun i => x i / k) i)
    (by rw [← hj]; exact Nat.div_le_div_right (least_le x j))

private theorem minimum_fits {D : ℕ} [NeZero D] (w : ℕ) (x : Fin D → ℕ)
    (h : ∀ i, x i < 2^w) (is : List (Fin D)) : (minimumExpr is).Fits w x := by
  induction is with
  | nil => exact h 0
  | cons i is ih => exact ⟨h i, ih, (min_le_left _ _).trans_lt (h i)⟩

/-- Public expression for multiplication by a fixed small layout constant. -/
def scaleExpr {I : Type*} (i : I) : ℕ → WidthExpr I
  | 0 => .const 0
  | k+1 => .binary .add (scaleExpr i k) (.field i)

/-- Scaling reads one field and returns its full natural multiple. -/
theorem scale_eval {I : Type*} (x : I → ℕ) (i : I) (k : ℕ) :
    (scaleExpr i k).eval x = k*x i := by
  induction k with
  | zero => simp [scaleExpr,WidthExpr.eval]
  | succ k ih => simp [scaleExpr,WidthExpr.eval,Op.apply,ih,Nat.succ_mul]

/-- Every intermediate multiple fits whenever the field and final product fit. -/
theorem scale_fits {I : Type*} (w : ℕ) (x : I → ℕ) (i : I) (k : ℕ)
    (h : x i < 2^w) (hk : k*x i < 2^w) : (scaleExpr i k).Fits w x := by
  induction k with
  | zero => exact Nat.two_pow_pos _
  | succ k ih =>
    rw [Nat.succ_mul] at hk
    exact ⟨ih (by omega), h, by simpa only [Op.apply, WidthExpr.eval, scale_eval] using hk⟩

/-- The first word is the actual profile multiplicity and the second is the width selected
in each direction. The polynomial depends only on the fixed crossing dimension and block
width. -/
theorem seed_frames (D m : ℕ) [NeZero D] (hm : 0 < m) :
    ∃ C e : ℕ, ∀ w, ∃ f : Frame (Fin D × Fin w) (Fin w ⊕ Fin w),
      f.size ≤ C*(w+1)^e ∧ ∀ x : Fin D × Fin w → Bool,
        let cnt := fun i => value (fun j => x (i,j))
        let b := Epoch.leastCount (fun i => cnt i / D) / m
        value (f.eval x ∘ Sum.inl) = b ∧ value (f.eval x ∘ Sum.inr) = b*m := by
  obtain ⟨c,e,hd⟩ := fixed_division_frames (D*m) (Nat.mul_pos (NeZero.pos _) hm)
  let q := minimumExpr (List.finRange D)
  let s := scaleExpr () m
  let constant := (q.nodes + s.nodes) * 100 + c
  refine ⟨constant, max 2 e, fun w => ?_⟩
  obtain ⟨div, hc, hv⟩ := hd w
  let mult := (s.frame w).subst (Frame.initial (fun i : Unit × Fin w => i.2))
  let both := Crossing.parallelFrame (Frame.initial (id : Fin w → Fin w)) mult
  let result := both.subst (div.subst (q.frame w))
  refine ⟨result, ?_, fun x => ?_⟩
  · simp only [result, Frame.subst_size, both, Crossing.parallelFrame_size, mult,
      Frame.initial_size, zero_add]

    have h₂ : (w+1)^2 ≤ (w+1)^(max 2 e) := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have he : (w+1)^e ≤ (w+1)^(max 2 e) := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hq := (q.frame_size w).trans (Nat.mul_le_mul_left q.nodes (Nat.mul_le_mul_left 100 h₂))
    have hs := (s.frame_size w).trans (Nat.mul_le_mul_left s.nodes (Nat.mul_le_mul_left 100 h₂))
    have hdiv := hc.trans (Nat.mul_le_mul_left c he)
    dsimp [constant]
    nlinarith only [hq,hs,hdiv]
  · let cnt := fun i => value (fun j => x (i,j))
    let y := (div.subst (q.frame w)).eval x
    let b := Epoch.leastCount (fun i => cnt i / D) / m
    have hq : value ((q.frame w).eval x) = Epoch.leastCount cnt :=
      (q.frame_value w x (minimum_fits w cnt (fun i => value_lt _) _)).trans (minimum_eq cnt)
    have hy : value y = b := by
      have hfun : y = div.eval ((q.frame w).eval x) := funext fun j => Frame.subst_eval _ _ _ _
      rw [hfun,hv,hq]
      simp only [b,least_div,Nat.div_div_eq_div_mul]
    have hb : b*m < 2^w := (Nat.div_mul_le_self _ _).trans_lt
      ((least_le (fun i => cnt i / D) 0).trans_lt ((Nat.div_le_self _ _).trans_lt (value_lt _)))
    let z := fun i : Unit × Fin w => y i.2
    have hsz : s.Fits w (fun u => value (fun j => z (u,j))) :=
      scale_fits w _ () m (value_lt _) (by change m * value y < 2^w; rw [hy,Nat.mul_comm]; exact hb)
    have hleft : result.eval x ∘ Sum.inl = y := by
      funext j
      simp [result, both, y, Frame.subst_eval, Crossing.parallelFrame_eval_inl]
    have hright : result.eval x ∘ Sum.inr = (s.frame w).eval z := by
      funext j
      simp only [Function.comp_apply,result,Frame.subst_eval,both,Crossing.parallelFrame_eval_inr,
        mult]
      congr 1
      funext i
      simp [z,y]
    refine ⟨hleft ▸ hy, ?_⟩
    rw [hright, s.frame_value w z hsz, scale_eval]
    change m * value y = b*m
    rw [hy,Nat.mul_comm]

end Packing.PoolCircuit

end BorderVNP
end Computability
end OAI

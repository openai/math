import OAI.Optimization.LinearProgramming.PriceGame.LearningRepresentatives
import OAI.Optimization.LinearProgramming.PriceGame.LearningCount

/-! # Adaptive disagreements in a nested sequence of true cells -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning

open Finset

/-- The range of `v i - v j` is an integer width in a feasible closed cell. -/
def featureWidth {n} (t : Paths.Table n) (i j : Fin n) : ℕ :=
  (Paths.read t j i + Paths.read t i j).toNat

variable {p R : ℕ} {a : Fin (p+1)} {os os' : List (Observation (p+1))}
  {t t' : Paths.Table (p+1)}

theorem cast_featureWidth (ht : cellTable R a os = some t) (i j : Fin (p+1)) :
    ((featureWidth t i j : ℕ) : ℤ) = Paths.read t j i + Paths.read t i j := by
  apply Int.toNat_of_nonneg
  obtain ⟨hd,htri⟩ := cellTable_geometry ht
  simpa [hd] using htri j i j

lemma inCell_mono (hsub : os ⊆ os') {v} (h' : inCell R a os' v) : inCell R a os v :=
  ⟨h'.1,h'.2.1,fun o ho => h'.2.2 o (hsub ho)⟩

/-- Widths start at most `2R`, including features involving the dummy vertex. -/
theorem featureWidth_le_two_mul (ht : cellTable R a os = some t) (i j : Fin (p+1)) :
    featureWidth t i j ≤ 2*R := by
  obtain ⟨_,⟨v,hv,hlo⟩,w,hw,hhi⟩ := feature_range ht i j
  have hb (i : Fin (p+1)) : (boxUpper R a i : ℚ) - (boxLower a i : ℚ) ≤ R := by
    by_cases he : i = a <;> simp [boxUpper,boxLower,he]
  have hh : ((Paths.read t j i : ℚ) + (Paths.read t i j : ℚ)) ≤ 2*R := by
    linarith [(hv.2.1 i).1, (hv.2.1 j).2, (hw.2.1 i).2, (hw.2.1 j).1, hb i, hb j]
  have hInt : ((featureWidth t i j : ℕ) : ℤ) ≤ 2 * (R : ℤ) := by
    rw [cast_featureWidth ht]; exact_mod_cast hh
  exact_mod_cast hInt

/-- Adding adaptive thresholds can only decrease the feature range. -/
theorem featureWidth_mono (hsub : os ⊆ os') (ht : cellTable R a os = some t)
    (ht' : cellTable R a os' = some t') (i j : Fin (p+1)) :
    featureWidth t' i j ≤ featureWidth t i j := by
  obtain ⟨bound,_,_⟩ := feature_range ht i j
  obtain ⟨_,⟨v,hv,hlo⟩,w,hw,hhi⟩ := feature_range ht' i j
  have b1 := (bound v (inCell_mono hsub hv)).1
  have b2 := (bound w (inCell_mono hsub hw)).2
  have hh : ((Paths.read t' j i : ℚ) + (Paths.read t' i j : ℚ)) ≤
      (Paths.read t j i : ℚ) + (Paths.read t i j : ℚ) := by linarith
  have hInt : ((featureWidth t' i j : ℕ) : ℤ) ≤ ((featureWidth t i j : ℕ) : ℤ) := by
    rw [cast_featureWidth ht', cast_featureWidth ht]; exact_mod_cast hh
  exact_mod_cast hInt

/-- Every newly learned comparison that disagrees with the current representative
charges a positive integral width and contracts it by the claimed factor. -/
theorem observed_disagreement (hsub : os ⊆ os') (ht : cellTable R a os = some t)
    (ht' : cellTable R a os' = some t') (o : Observation (p+1)) (hmem : o ∈ os')
    (hdis : ¬ realizes o (representative (Paths.read t) a)) :
    0 < featureWidth t o.i o.j ∧
    (featureWidth t' o.i o.j : ℚ) ≤ (1 - 1 / (p + 1 : ℕ)) * (featureWidth t o.i o.j : ℚ) := by
  let c := representative (Paths.read t) a o.i - representative (Paths.read t) a o.j
  have hdis' : compare c o.threshold ≠ o.side := hdis
  obtain ⟨bound,_,_⟩ := feature_range ht o.i o.j
  obtain ⟨b',⟨v,hv,hlo⟩,w,hw,hhi⟩ := feature_range ht' o.i o.j
  have hlow := (bound v (inCell_mono hsub hv)).1
  have hhigh := (bound w (inCell_mono hsub hw)).2
  have hwidth := (b' w hw).1
  rw [hlo] at hlow
  rw [hhi] at hhigh hwidth
  have hleft : compare (-(Paths.read t' o.i o.j : ℚ)) o.threshold = o.side := by
    rw [← hlo]; exact accepts_sound (hv.2.2 o hmem)
  have hright : compare (Paths.read t' o.j o.i : ℚ) o.threshold = o.side := by
    rw [← hhi]; exact accepts_sound (hw.2.2 o hmem)
  obtain ⟨diag,tri⟩ := cellTable_geometry ht
  have margin := representative_feature_margin diag tri a o.i o.j
  have contraction := exceptional_width (k := ((p + 1 : ℕ) : ℚ)) ⟨hlow,hwidth,hhigh⟩
    (by exact_mod_cast (show 1 ≤ p + 1 by omega)) margin rfl (hright.trans hleft.symm)
    (fun hh => hdis' (hh.trans hleft))
  have castQ {os : List (Observation (p+1))} {u : Paths.Table (p+1)}
      (ho : cellTable R a os = some u) :
      (featureWidth u o.i o.j : ℚ) = (Paths.read u o.j o.i : ℚ) + (Paths.read u o.i o.j : ℚ) := by
    exact_mod_cast cast_featureWidth ho o.i o.j
  constructor
  · by_contra! h
    have hz : (featureWidth t o.i o.j : ℚ) = 0 := by exact_mod_cast (Nat.eq_zero_of_le_zero h)
    rw [castQ ht] at hz
    obtain ⟨hcl,hcu⟩ := bound _ (representative_inCell ht)
    have hc : c = -(Paths.read t' o.i o.j : ℚ) := by dsimp [c]; linarith
    exact hdis' (hc ▸ hleft)
  · simpa only [castQ ht', castQ ht, sub_neg_eq_add] using contraction

/-- The exception bound for an actual history of compiled cells, one per skeleton. All
selections and new thresholds may depend on past trials. Every exceptional interval ends
with a witnessed comparison mismatch; uncharged skeletons need only retain their cuts. -/
theorem adaptive_exception_bound {S : Type*} [Fintype S] [DecidableEq S]
    (p : S → ℕ) (R T : ℕ) (hR : 0 < R) (a : ∀ s, Fin (p s+1))
    (history : ∀ s, ℕ → List (Observation (p s+1)))
    (tables : ∀ s, ℕ → Paths.Table (p s+1))
    (compiled : ∀ s n, cellTable R (a s) (history s n) = some (tables s n))
    (retains : ∀ s n, n < T → history s n ⊆ history s (n+1))
    (charged : ℕ → S) (obs : ∀ n, Observation (p (charged n)+1))
    (new : ∀ n, n < T → obs n ∈ history (charged n) (n+1))
    (wrong : ∀ n, n < T → ¬ realizes (obs n)
      (representative (Paths.read (tables (charged n) n)) (a (charged n)))) :
    (T : ℝ) ≤ ∑ s : S, ((p s + 1 : ℕ) : ℝ)^2 *
      (1 + ((p s : ℝ) + 1) * Real.log (2*R)) := by
  let I := (s : S) × (Fin (p s+1) × Fin (p s+1))
  let f (n) : I := ⟨charged n,(obs n).i,(obs n).j⟩
  let widths (i : I) (n : ℕ) := featureWidth (tables i.1 n) i.2.1 i.2.2
  have shrink (n) (hn : n < T) := observed_disagreement (retains (charged n) n hn)
    (compiled (charged n) n) (compiled (charged n) (n+1)) (obs n) (new n hn) (wrong n hn)
  have total := Count.exceptional_trials_le (ι := I) (fun i => p i.1) R T hR f widths
    (fun i => featureWidth_le_two_mul (compiled _ _) _ _)
    (fun i n hn => featureWidth_mono (retains _ _ hn) (compiled _ _) (compiled _ _) _ _)
    (fun n hn => (shrink n hn).1) (fun n hn => by
      dsimp only [widths, f]
      have hreal := (Rat.cast_le (K := ℝ)).mpr (shrink n hn).2
      push_cast at hreal
      simpa only [Nat.cast_add, Nat.cast_one] using hreal)
  simpa [I, Fintype.sum_sigma, Fintype.sum_prod_type, sq, mul_add, mul_assoc] using total

end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI

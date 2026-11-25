import OAI.Optimization.LinearProgramming.PriceGame.MomentThreshold
import OAI.Optimization.LinearProgramming.PriceGame.MomentLocal

/-! Finite recursive score transcripts for Section 5. A transcript stores the local gain produced
by each probe; admissibility ties it to the incoming weights. Child calls receive the updated
deeper weights, including the scores from every earlier child. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

universe u

open Finset

def probeAt {n : ℕ} {α : Type*} [Zero α] (f : Fin n → α) (t : ℕ) : α :=
  if h : t < n then f ⟨t, h⟩ else 0

@[simp] theorem probeAt_fin {n : ℕ} {α : Type*} [Zero α] (f : Fin n → α) (t : Fin n) :
    probeAt f t.val = f t := by simp [probeAt, t.isLt]

def localPart {E : Type*} (mask : E → Bool) (w : E → ℝ) (e : E) : ℝ :=
  if mask e then w e else 0

def deepPart {E : Type*} (mask : E → Bool) (w : E → ℝ) (e : E) : ℝ :=
  if mask e then 0 else w e

/-- Experts here may be identified by any finite label type, including distinct
identifiers for experts with identical raw values. -/
inductive Trial (E : Type u) (r : ℕ) : Type u
  | leaf
  | node (mask : E → Bool) (gain : Fin r → E → ℚ) (children : Fin (2 * r) → Trial E r)

def meanQ (k : ℕ) (f : ℕ → ℚ) : ℚ := (∑ t ∈ range k, f t) / k

theorem cast_meanQ (k : ℕ) (f : ℕ → ℚ) :
    ((meanQ k f : ℚ) : ℝ) = (∑ t ∈ range k, (f t : ℝ)) / k := by
  unfold meanQ
  push_cast
  rfl

def Trial.score {E : Type*} {r : ℕ} (C σ : ℚ) : Trial E r → E → ℕ
  | .leaf, _ => 0
  | .node mask gain children, e =>
    if mask e then rationalScore C σ (meanQ r fun t => probeAt gain t e)
    else rationalScore C σ (meanQ (2 * r) fun t => (probeAt (fun k => (children k).score C σ) t e : ℕ))

def gainAt {E : Type*} {r : ℕ} (gain : Fin r → E → ℚ) (j : ℕ) (e : E) : ℝ :=
  (probeAt gain j e : ℚ)

def childScoreAt {E : Type*} {r : ℕ} (C σ : ℚ) (children : Fin (2 * r) → Trial E r)
    (j : ℕ) (e : E) : ℕ := probeAt (fun k => (children k).score C σ) j e

theorem Trial.score_node {E : Type*} {r : ℕ} (C σ : ℚ) (mask : E → Bool)
    (gain : Fin r → E → ℚ) (children : Fin (2 * r) → Trial E r) (e : E) :
    (Trial.node mask gain children).score C σ e =
      if mask e then roundedScore C σ ((∑ t ∈ range r, gainAt gain t e) / (r : ℝ))
      else roundedScore C σ ((∑ t ∈ range (2 * r), (childScoreAt C σ children t e : ℝ)) /
        ((2 * r : ℕ) : ℝ)) := by
  simp only [Trial.score, ← roundedScore_ratCast, cast_meanQ, Rat.cast_natCast, childScoreAt, gainAt]

/-- Admissibility only checks the geometric feedback's bound, its balance against current
weights, and its recursively correct use of the actual incoming weights. -/
def Trial.Admissible {E : Type*} [Fintype E] {r : ℕ} (C σ : ℚ) (η : ℝ) :
    Trial E r → (E → ℝ) → Prop
  | .leaf, _ => True
  | .node mask gain children, w =>
    (∀ t < r, ∀ e, |gainAt gain t e| ≤ 1) ∧
    (∀ t < r, ∑ e, localWeight η (localPart mask w) (gainAt gain) t e * gainAt gain t e = 0) ∧
    ∀ t : Fin (2 * r), (children t).Admissible C σ η
      (deepWeight (deepPart mask w) (childScoreAt C σ children) t)

theorem sum_split_moment {E : Type*} [Fintype E] (w : E → ℝ) (mask : E → Bool)
    (localScore deepScore : E → ℕ) (B : ℝ)
    (hl : (∑ e, localPart mask w e * 2 ^ localScore e) ≤ B * ∑ e, localPart mask w e)
    (hd : (∑ e, deepPart mask w e * 2 ^ deepScore e) ≤ B * ∑ e, deepPart mask w e) :
    (∑ e, w e * 2 ^ (if mask e then localScore e else deepScore e)) ≤ B * ∑ e, w e := by
  have h := add_le_add hl hd
  rw [← mul_add, ← sum_add_distrib, ← sum_add_distrib] at h
  convert h using 1
  · apply sum_congr rfl
    intro e _
    cases he : mask e <;> simp [localPart, deepPart, he]
  · congr 1
    apply sum_congr rfl
    intro e _
    cases he : mask e <;> simp [localPart, deepPart, he]

/-- The two group estimates imply the score moment simultaneously at every node of a trial.
This structural induction admits arbitrary adaptive sequences of balanced probe replies. -/
theorem Trial.moment_of_groups {E : Type*} [Fintype E] {r : ℕ} (C σ : ℚ) (η τ : ℝ)
    (hτ : 0 ≤ τ)
    (hl : ∀ (w : E → ℝ) (g : ℕ → E → ℝ), (∀ e, 0 ≤ w e) →
      (∀ t < r, ∀ e, |g t e| ≤ 1) →
      (∀ t < r, ∑ e, localWeight η w g t e * g t e = 0) →
      (∑ e, w e * (2 : ℝ) ^ roundedScore C σ ((∑ t ∈ range r, g t e) / (r : ℝ))) ≤
        (2 : ℝ) ^ τ * ∑ e, w e)
    (hd : ∀ (w : E → ℝ) (s : ℕ → E → ℕ), (∀ e, 0 ≤ w e) →
      (∀ j < 2 * r, (∑ e, deepWeight w s j e * (2 : ℝ) ^ s j e) ≤
        (2 : ℝ) ^ τ * ∑ e, deepWeight w s j e) →
      (∑ e, w e * (2 : ℝ) ^ roundedScore C σ
        ((∑ j ∈ range (2 * r), (s j e : ℝ)) / ((2 * r : ℕ) : ℝ))) ≤ (2 : ℝ) ^ τ * ∑ e, w e)
    (tr : Trial E r) (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) (ha : tr.Admissible C σ η w) :
    (∑ e, w e * (2 : ℝ) ^ tr.score C σ e) ≤ (2 : ℝ) ^ τ * ∑ e, w e := by
  induction tr generalizing w with
  | leaf =>
    simp only [Trial.score, pow_zero, mul_one]
    exact le_mul_of_one_le_left (sum_nonneg fun e _ => hw e)
      (Real.one_le_rpow (by norm_num) hτ)
  | node mask gain children ih =>
    obtain ⟨hg, hbal, hc⟩ := ha
    simp only [Trial.score_node]
    apply sum_split_moment
    · apply hl _ _ _ hg hbal
      intro e
      simp only [localPart]
      split <;> simp [hw e]
    · apply hd
      · intro e
        simp only [deepPart]
        split <;> simp [hw e]
      · intro t ht
        let k : Fin (2 * r) := ⟨t, ht⟩
        have hw' (e : E) : 0 ≤ deepWeight (deepPart mask w) (childScoreAt C σ children) t e := by
          apply deepWeight_nonneg
          simp only [deepPart]
          split <;> simp [hw e]
        have hi := ih k _ hw' (hc k)
        have hs (e : E) : childScoreAt C σ children t e = (children k).score C σ e := by
          simp [childScoreAt, probeAt, ht, k]
        simpa only [hs] using hi

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI

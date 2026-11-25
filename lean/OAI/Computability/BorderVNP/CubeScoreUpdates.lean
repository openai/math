import OAI.Computability.BorderVNP.CubeSparseRecords
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Updating the balancing score from incident descriptors

A trial label changes only the mean records touching that cell and the covariance
records indexed at it. One can consequently keep two running values per bin and
obtain the exact next score from the local lists. All arithmetic in the public
update is rational, including for the original integer cable widths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Balancing

open Finset
open scoped BigOperators

variable {C L E : Type*} [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L]
  [Fintype E] [DecidableEq E]

/-- Rational mean of one bit-pattern after pinning a partial labeling. -/
def probability (p : Pattern C L) (s : Finset C) (x : C → L) : ℚ :=
  if ∀ c ∈ p.sites ∩ s, x c = p.value c then
    (Fintype.card L : ℚ)⁻¹ ^ (p.sites \ s).card else 0

/-- Rational joint mean for two bit-patterns. -/
def joint (p q : Pattern C L) (s : Finset C) (x : C → L) : ℚ :=
  if ∀ c ∈ p.sites ∩ q.sites, p.value c = q.value c then
    probability ⟨p.sites ∪ q.sites, fun c ↦ if c ∈ p.sites then p.value c else q.value c⟩ s x
  else 0

/-- Rational public arithmetic gives the exact real conditional mean. -/
theorem probability_cast (p : Pattern C L) (s : Finset C) (x : C → L) :
    (probability p s x : ℝ) = pinnedChance p s x := by
  unfold probability pinnedChance
  split <;> simp

/-- Rational joint means give the actual real conditional joint means. -/
theorem joint_cast (p q : Pattern C L) (s : Finset C) (x : C → L) :
    (joint p q s x : ℝ) = jointChance p q s x := by
  unfold joint jointChance
  split
  · exact probability_cast _ _ _
  · norm_num

/-- One compressed mean record with rational multiplicity. -/
def meanRecord (p : E → Pattern C L) (w : E → ℚ) (s : Finset C) (x : C → L) (e : E) :=
  w e * probability (p e) s x

/-- One covariance record for an ordered pair of compressed descriptors. -/
def covRecord (p : E → Pattern C L) (w : E → ℚ) (s : Finset C) (x : C → L) (e : E × E) :=
  w e.1*w e.2*(joint (p e.1) (p e.2) s x -
    probability (p e.1) s x * probability (p e.2) s x)

/-- The mean and variance values maintained for one label bin. -/
def moments (p : E → Pattern C L) (w : E → ℚ) (s : Finset C) (x : C → L) : ℚ × ℚ :=
  (∑ e, meanRecord p w s x e, ∑ e ∈ overlapRecords (fun i ↦ (p i).sites), covRecord p w s x e)

/-- Exact squared-deviation score from the two cached rational values. -/
def score (m : ℚ) (v : ℚ × ℚ) := (v.1-m)^2 + v.2

omit [DecidableEq E] in
/-- The cached rational score equals the conditional mean of the squared deviation. -/
theorem score_cast [Nonempty L] (p : E → Pattern C L) (w : E → ℚ) (m : ℚ)
    (s : Finset C) (x : C → L) :
    (score m (moments p w s x) : ℝ) =
      𝔼 y, ((∑ e, (w e : ℝ)*hit (p e) (fill s x y))-(m:ℝ))^2 := by
  rw [sparse_conditional_score]
  simp only [score,moments,meanRecord,covRecord,overlapRecords,Finset.sum_filter]
  simp only [Rat.cast_add,Rat.cast_sub,Rat.cast_pow,Rat.cast_sum,Rat.cast_mul,apply_ite Rat.cast,
    Rat.cast_zero,joint_cast,probability_cast,Fintype.sum_prod_type]

private theorem sum_update {T : Type*} [DecidableEq T] (I J : Finset T) (hJ : J ⊆ I)
    (f g : T → ℚ) (hout : ∀ e ∈ I, e ∉ J → f e = g e) :
    (∑ e ∈ I, f e) + ∑ e ∈ J, (g e-f e) = ∑ e ∈ I, g e := by
  rw [← Finset.sum_sdiff hJ (f := f), ← Finset.sum_sdiff hJ (f := g),
    Finset.sum_sub_distrib]
  have eq := Finset.sum_congr (s₁ := I \ J) rfl (fun e he ↦ hout e (mem_sdiff.mp he).1 (mem_sdiff.mp he).2)
  rw [eq]; ring

/-- Update the two public cached values using only incident mean and covariance
record IDs. Both lists can be constructed from the public endpoint data in advance. -/
def updateMoments (p : E → Pattern C L) (w : E → ℚ) (s : Finset C) (x : C → L) (c : C) (v : L)
    (meanIDs : Finset E) (covIDs : Finset (E × E)) (old : ℚ × ℚ) : ℚ × ℚ :=
  let s' := insert c s
  let x' := Function.update x c v
  (old.1 + ∑ e ∈ meanIDs, (meanRecord p w s' x' e - meanRecord p w s x e),
    old.2 + ∑ e ∈ covIDs, (covRecord p w s' x' e - covRecord p w s x e))

/-- The public endpoint-indexed update agrees with recalculating the full moments. -/
theorem updateMoments_eq (p : E → Pattern C L) (w : E → ℚ) (s : Finset C) (x : C → L)
    (c : C) (v : L) :
    let meanIDs := incident (fun e ↦ (p e).sites) c
    let covIDs := (overlapRecords (fun e ↦ (p e).sites)).filter fun e ↦
      c ∈ (p e.1).sites ∪ (p e.2).sites
    updateMoments p w s x c v meanIDs covIDs (moments p w s x) =
      moments p w (insert c s) (Function.update x c v) := by
  dsimp only [moments,updateMoments]
  apply Prod.ext
  · apply sum_update _ _ (Finset.subset_univ _)
    intro e _ h
    have hc : c ∉ (p e).sites := by simpa [incident] using h
    unfold meanRecord
    congr 1
    apply Rat.cast_injective (α := ℝ)
    rw [probability_cast,probability_cast,pinnedChance_unchanged _ _ _ _ hc]
  · apply sum_update _ _ (Finset.filter_subset _ _)
    intro e he hn
    have hc : c ∉ (p e.1).sites ∪ (p e.2).sites := fun h ↦ hn (mem_filter.mpr ⟨he,h⟩)
    unfold covRecord
    congr 1
    apply Rat.cast_injective (α := ℝ)
    push_cast
    simp only [joint_cast,probability_cast,covariance_unchanged _ _ _ _ _ hc v]

end Cube.Balancing

end BorderVNP
end Computability
end OAI

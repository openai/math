import OAI.Hierarchy.DescentPackingColors
import OAI.Hierarchy.DescentWholeItems

namespace OAI
/-! # Matched bundle mass for a common affine colony coloring -/

namespace Hierarchy.DescentMatchedCost
open DescentWalshTables DescentPacking Finset
open scoped BigOperators

noncomputable def slab {k : ℕ} (p : Bits k → Bool) (A : Bits k → ℕ) :=
  ∑ i, if p i then A i else 0

/-- An affine color with the stated imbalance retains this many bundles on both sides. -/
theorem colored_overlap_of_bound {k : ℕ} {C : Type*} [Fintype C] (A : C → Bits k → ℕ)
    (B : ℕ) (a : Bits k) (b : ZMod 2)
    (h : ∑ c, |∑ i, sign (binaryRow a i+b)*(A c i:ℝ)| ≤
      Real.sqrt ((B:ℝ)*Fintype.card C*∑ c,∑ i,(A c i:ℝ))) :
    let thick := fun i => decide (binaryRow a i+b=0)
    (∑ c,∑ i, (A c i:ℝ)) - Real.sqrt ((B:ℝ)*Fintype.card C*∑ c, ∑ i, (A c i:ℝ)) ≤
      2*∑ c, (min (slab thick (A c)) (slab (fun i => !(thick i)) (A c)):ℝ) := by
  classical
  let thick := fun i => decide (binaryRow a i+b=0)
  change _ ≤ 2*∑ c, min (slab thick (A c):ℝ) (slab (fun i => !(thick i)) (A c):ℝ)
  have both (c : C) : (slab thick (A c):ℝ)+(slab (fun i => !(thick i)) (A c):ℝ)=∑ i,(A c i:ℝ) := by
    simp only [slab,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hi : binaryRow a i+b=0 <;> simp [thick,hi]
  have delta (c : C) : (slab thick (A c):ℝ)-(slab (fun i => !(thick i)) (A c):ℝ)=
      ∑ i, sign (binaryRow a i+b)*(A c i:ℝ) := by
    simp only [slab,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,←sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hi : binaryRow a i+b=0 <;> simp [thick,sign,hi]
  have point (c : C) : (∑ i,(A c i:ℝ)) - |∑ i,sign (binaryRow a i+b)*(A c i:ℝ)| =
      2*min (slab thick (A c):ℝ) (slab (fun i => !(thick i)) (A c):ℝ) := by
    rw [← both,← delta]
    by_cases less : (slab thick (A c):ℝ) ≤ (slab (fun i => !(thick i)) (A c):ℝ)
    · rw [min_eq_left less,abs_of_nonpos (sub_nonpos.mpr less)];ring
    · rw [min_eq_right (le_of_not_ge less),abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge less))];ring
  have agg := sum_congr (s₁:=univ) rfl (fun c _ => point c)
  rw [sum_sub_distrib,←Finset.mul_sum] at agg
  linarith only [h,agg]

/-- One binary affine sheet leaves this much overlap in the actual whole-bundle counts. -/
theorem colored_overlap {k : ℕ} {C : Type*} [Fintype C] (A : C → Bits k → ℕ)
    (B : ℕ) (cap : ∀ c i, A c i ≤ B) :
    ∃ (a : Bits k) (b : ZMod 2),
      let thick := fun i => decide (binaryRow a i+b=0)
      (∑ c,∑ i, (A c i:ℝ)) - Real.sqrt ((B:ℝ)*Fintype.card C*∑ c, ∑ i, (A c i:ℝ)) ≤
        2*∑ c, (min (slab thick (A c)) (slab (fun i => !(thick i)) (A c)):ℝ) := by
  obtain ⟨a,b,h⟩ := DescentPackingColors.exists_coloring (fun c i => (A c i:ℝ)) B
    (fun _ _ => Nat.cast_nonneg _) (fun c i => by exact_mod_cast cap c i)
  exact ⟨a,b,colored_overlap_of_bound A B a b h⟩

/-- Sum the actual greedy whole-item assignments. Only the capacities and the retained pair
count are needed to plug in the discrete occurrence-level pack construction. -/
theorem whole_pack_loss {C V I : Type*} [Fintype C] [Fintype V] [DecidableEq V]
    (amount : C → I → ℕ) (items : C → List I) (capacity : C → V → ℕ) (B : ℕ)
    (small : ∀ c i, i ∈ items c → amount c i ≤ 2*B) :
    ∑ c, min ((items c).map (amount c)).sum (∑v,capacity c v) ≤
      (∑ c,∑v,assigned (amount c) v (pack (amount c) (items c) (capacity c)).decisions) +
          2*B*Fintype.card V*Fintype.card C := by
  have h := sum_le_sum (s:=univ) (fun c _ => packing_loss (amount c) (items c) (capacity c) (2*B) (small c))
  rw [sum_add_distrib] at h
  simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

end Hierarchy.DescentMatchedCost

end OAI

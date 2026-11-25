import OAI.Hierarchy.DescentGLConditional
import OAI.Hierarchy.DescentGLSelection
import Mathlib.Algebra.BigOperators.Field

namespace OAI
/-! # Collision potentials in a row-conditioned ensemble of binary layouts -/

namespace Hierarchy.DescentGL
open scoped Classical BigOperators
noncomputable section

private theorem rows_iff_head {h r : ℕ} (L base : Layout (h+r)) :
    (∀ i<h, layoutRow L i=layoutRow base i) ↔
      ∀ v, (splitRows h r (L v)).1=(splitRows h r (base v)).1 := by
  constructor
  · intro rows v
    funext i
    have hi : i.val<h+r := by omega
    have idx : i.castAdd r=⟨i.val,hi⟩ := Fin.ext rfl
    change L v (i.castAdd r)=base v (i.castAdd r)
    simpa only [layoutRow, dite_eq_left hi, idx] using congrFun (rows i.val i.isLt) v
  · intro head i hi
    funext v
    have hi' : i<h+r := by omega
    let l : Fin h := ⟨i,hi⟩
    have idx : l.castAdd r=⟨i,hi'⟩ := Fin.ext rfl
    have same := congrFun (head v) l
    change L v (l.castAdd r)=base v (l.castAdd r) at same
    simpa only [layoutRow, dite_eq_left hi', idx] using same

/-- Rowwise agreement and agreement of the leading block give the same ensemble. -/
theorem prefixMean_eq_completions {h r : ℕ} (cost : Layout (h+r) → ℝ) (base : Layout (h+r)) :
    prefixMean cost base h =
      (∑ L : Completions h r base, cost L.val) / Fintype.card (Completions h r base) := by
  let s := Finset.univ.filter fun L : Layout (h+r) => ∀ i<h,layoutRow L i=layoutRow base i
  have mem (L : Layout (h+r)) :
      L∈s ↔ ∀ v,(splitRows h r (L v)).1=(splitRows h r (base v)).1 := by
    simpa [s] using rows_iff_head L base
  have count : s.card=Fintype.card (Completions h r base) := by
    rw [Fintype.card_subtype]
    congr 1
    ext L
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using mem L
  rw [prefixMean_eq_sum_of_mem cost base s (fun L => by simp [s])]
  rw [Finset.sum_subtype s mem cost, count]

/-- The conditional expectation of the collision indicator at any later depth.
This includes differences already separated by the fixed head. -/
theorem prefixMean_collision {h r j : ℕ} (hj : j≤r) (base : Layout (h+r)) (d : Nonzero (h+r)) :
    prefixMean (fun L => if headRows (Nat.add_le_add_left hj h) (L d.val)=0 then 1 else 0) base h =
      if (splitRows h r (base d.val)).1=0 then
        ((2^(r-j)-1:ℕ):ℝ) / ((2^r-1:ℕ):ℝ) else 0 := by
  rw [prefixMean_eq_completions]
  split_ifs with survives
  · simpa only [Finset.sum_boole] using conditional_collision_probability hj base d survives
  · have miss (L : Completions h r base) : headRows (Nat.add_le_add_left hj h) (L.val d.val) ≠ 0 := by
      intro hit
      apply survives
      rw [←L.property d.val]
      funext i
      exact congrFun hit (i.castAdd j)
    simp [miss]

/-- At its current depth the collision potential equals the actual indicator,
including the case in which every row has already been fixed. -/
theorem prefixMean_current_collision {h r : ℕ} (base : Layout (h+r)) (d : Nonzero (h+r)) :
    prefixMean (fun L => if (splitRows h r (L d.val)).1=0 then 1 else 0) base h =
      if (splitRows h r (base d.val)).1=0 then 1 else 0 := by
  rw [prefixMean_eq_completions]
  let : Nonempty (Completions h r base) := ⟨⟨base, fun _ => rfl⟩⟩
  have identical (L : Completions h r base) :
      (splitRows h r (L.val d.val)).1=(splitRows h r (base d.val)).1 := L.property d.val
  simp only [identical, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast (Fintype.card_pos (α:=Completions h r base)).ne')]

/-- Every contribution from a shallower level has already been determined. -/
theorem prefixMean_earlier_collision {h r j : ℕ} (hj : j≤h) (base : Layout (h+r))
    (d : Nonzero (h+r)) :
    prefixMean (fun L =>
      if headRows (hj.trans (Nat.le_add_right h r)) (L d.val)=0 then 1 else 0) base h =
      if headRows (hj.trans (Nat.le_add_right h r)) (base d.val)=0 then 1 else 0 := by
  rw [prefixMean_eq_completions]
  let : Nonempty (Completions h r base) := ⟨⟨base, fun _ => rfl⟩⟩
  have identical (L : Completions h r base) :
      headRows (hj.trans (Nat.le_add_right h r)) (L.val d.val) =
      headRows (hj.trans (Nat.le_add_right h r)) (base d.val) := by
    funext i
    exact congrFun (L.property d.val) (i.castLE hj)
  simp only [identical, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast (Fintype.card_pos (α:=Completions h r base)).ne')]

/-- The same pointwise conditional law for a weighted collection of nonzero differences. -/
theorem prefixMean_weighted_collisions {h r j : ℕ} (hj : j≤r) (base : Layout (h+r))
    (weights : Nonzero (h+r) → ℝ) :
    prefixMean (fun L => ∑ d : Nonzero (h+r), weights d *
      (if headRows (Nat.add_le_add_left hj h) (L d.val)=0 then 1 else 0)) base h =
    ∑ d : Nonzero (h+r), weights d * (if (splitRows h r (base d.val)).1=0 then
      ((2^(r-j)-1:ℕ):ℝ) / ((2^r-1:ℕ):ℝ) else 0) := by
  simp_rw [←prefixMean_collision hj base]
  simp only [prefixMean_eq_completions]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [←Finset.mul_sum, mul_div_assoc]


end
end Hierarchy.DescentGL

end OAI

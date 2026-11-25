import OAI.Computability.BorderVNP.CubeConditioning
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange

/-!
# Deterministic minimization of conditional label scores

Section 8.1 fixes the labels in a public order, breaking ties by label order.
An explicit finite minimum and the tower identity for one uniform coordinate
show that the completed labeling costs at most the initial mean. The conditional
scores for cable and data bins are the sparse expressions in `CubeConditioning`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

/-- Find the first minimum by scanning the finite indices in their natural order. -/
def firstMinimum {β : Type*} [LinearOrder β] {n : ℕ} (f : Fin (n+1) → β) : Fin (n+1) :=
  ((List.finRange (n+1)).argmin f).getD 0

/-- The result of the scan has value no greater than any other index. -/
theorem firstMinimum_le {β : Type*} [LinearOrder β] {n : ℕ} (f : Fin (n+1) → β)
    (i : Fin (n+1)) : f (firstMinimum f) ≤ f i := by
  cases h : (List.finRange (n+1)).argmin f with
  | none =>
    have hm := List.mem_finRange i
    rw [List.argmin_eq_none.mp h] at hm
    contradiction
  | some j =>
    simpa only [firstMinimum,h,Option.getD_some] using
      List.le_of_mem_argmin (List.mem_finRange i) (show j ∈ (List.finRange (n+1)).argmin f from h)

namespace Balancing

open scoped BigOperators
open Finset

variable {C L : Type*} [Fintype C] [DecidableEq C] [Fintype L] [Nonempty L]

/-- Conditional mean of an arbitrary score, given the current fixed labels. -/
noncomputable def conditioned (f : (C → L) → ℝ) (s : Finset C) (x : C → L) : ℝ :=
  𝔼 y, f (fill s x y)

private def coordinateSwap (c : C) : L × (C → L) ≃ (C → L) × L where
  toFun p := (Function.update p.2 c p.1,p.2 c)
  invFun p := (p.1 c,Function.update p.1 c p.2)
  left_inv p := by simp
  right_inv p := by simp

private theorem mean_product {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a,b) := by
  simpa using Finset.expect_product univ univ f

/-- Averaging the possible values for one fresh cell recovers the parent score. -/
theorem conditioned_insert (f : (C → L) → ℝ) (s : Finset C) (x : C → L) {c : C}
    (hc : c ∉ s) : (𝔼 v, conditioned f (insert c s) (Function.update x c v)) =
      conditioned f s x := by
  let g (p : L × (C → L)) := f (fill (insert c s) (Function.update x c p.1) p.2)
  let h (p : (C → L) × L) := f (fill s x p.1)
  have same (p : L × (C → L)) : g p = h (coordinateSwap c p) := by
    apply congrArg f; funext j
    by_cases hj : j = c
    · subst j; simp [fill,coordinateSwap,hc]
    · simp [fill,coordinateSwap,hj]
  calc
    _ = 𝔼 p, g p := (mean_product g).symm
    _ = 𝔼 p, h p := Fintype.expect_equiv (coordinateSwap c) g h same
    _ = _ := by rw [mean_product]; simp only [h,Fintype.expect_const,conditioned]

/-- Fix labels in the supplied cell order, each time using the first minimizing symbol. -/
noncomputable def chooseLabels {z : ℕ} (f : (C → Fin (z+1)) → ℝ) :
    List C → Finset C → (C → Fin (z+1)) → (C → Fin (z+1))
  | [], _, x => x
  | c :: cs, s, x =>
    if c ∈ s then chooseLabels f cs s x else
      let score v := conditioned f (insert c s) (Function.update x c v)
      chooseLabels f cs (insert c s) (Function.update x c (firstMinimum score))

/-- Conditional expected cost never increases during the greedy traversal. -/
theorem chooseLabels_bound {z : ℕ} (f : (C → Fin (z+1)) → ℝ) (cs : List C)
    (s : Finset C) (x : C → Fin (z+1)) :
    conditioned f (cs.toFinset ∪ s) (chooseLabels f cs s x) ≤ conditioned f s x := by
  induction cs generalizing s x with
  | nil => simp [chooseLabels]
  | cons c cs ih =>
    by_cases hc : c ∈ s
    · have he : (c::cs).toFinset ∪ s = cs.toFinset ∪ s := by ext; simp; grind
      simpa only [chooseLabels,ite_eq_left hc,he] using ih s x
    · let score v := conditioned f (insert c s) (Function.update x c v)
      have hmean : score (firstMinimum score) ≤ 𝔼 v, score v := by
        apply Finset.le_expect univ_nonempty; exact fun v _ ↦ firstMinimum_le score v
      have hr : (𝔼 v, score v) = conditioned f s x := conditioned_insert f s x hc
      have he : (c::cs).toFinset ∪ s = cs.toFinset ∪ insert c s := by ext; simp
      rw [chooseLabels,ite_eq_right hc,he]
      exact (ih _ _).trans (hmean.trans hr.le)

/-- After every cell has been visited, the deterministic labeling's actual score
is at most the uniform mean. The initial labels are arbitrary. -/
theorem chooseLabels_le_mean {z : ℕ} (f : (C → Fin (z+1)) → ℝ) (cs : List C)
    (hcs : cs.toFinset = univ) (x : C → Fin (z+1)) :
    f (chooseLabels f cs ∅ x) ≤ 𝔼 y, f y := by
  have h := chooseLabels_bound f cs ∅ x
  have all (x y : C → Fin (z+1)) : fill univ x y = x := by ext; simp [fill]
  have none (x y : C → Fin (z+1)) : fill ∅ x y = y := by ext; simp [fill]
  simpa [hcs,conditioned,all,none,Fintype.expect_const] using h

end Balancing
end Cube

end BorderVNP
end Computability
end OAI

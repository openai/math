import Mathlib

/-! # The signed length-three paths in the cubic independent-set reduction

Summing the two internal occupation bits on a path forces equal endpoint
occupations. The negative sign for vacant endpoints occurs an even number
of times in each vertex chain.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace IndependentSetCubic
open scoped BigOperators Classical

abbrev Copies {V : Type*} (d : V → ℕ) := (v : V) × Fin (2 * d v + 1)
abbrev Links {V : Type*} (d : V → ℕ) := (v : V) × Fin (2 * d v)

variable {V R : Type*} {d : V → ℕ}

def prev (j : Links d) : Copies d := ⟨j.1, j.2.castSucc⟩
def nextCopy (j : Links d) : Copies d := ⟨j.1, j.2.succ⟩

def pathCompatible (a l r b : Bool) : Prop :=
  (a = true → l ≠ true) ∧ (l = true → r ≠ true) ∧ (r = true → b ≠ true)

variable [CommRing R]

def signWeight (b : Bool) : R := if b then -1 else 1

theorem signed_path (a b : Bool) :
    (∑ l : Bool, ∑ r : Bool, if pathCompatible a l r b then
      signWeight (R := R) l * signWeight r else 0) =
      if a = b then (if a then 1 else -1) else 0 := by
  cases a <;> cases b <;> simp [pathCompatible, signWeight]

private theorem contraction_at_copy [Fintype V] (c : Copies d → Bool) (v : R) :
    (∑ l : Links d → Bool, ∑ r : Links d → Bool,
      if ∀ j, pathCompatible (c (prev j)) (l j) (r j) (c (nextCopy j)) then
        v * (∏ j, signWeight (l j)) * ∏ j, signWeight (r j) else 0) =
    v * ∏ j : Links d, (if c (prev j) = c (nextCopy j) then
      (if c (prev j) then 1 else -1) else 0) := by
  let table (j : Links d) (a b : Bool) : R :=
    if pathCompatible (c (prev j)) a b (c (nextCopy j))
    then signWeight a * signWeight b else 0
  have factor (l r : Links d → Bool) :
      (if ∀ j, pathCompatible (c (prev j)) (l j) (r j) (c (nextCopy j)) then
        v * (∏ j, signWeight (l j)) * ∏ j, signWeight (r j) else 0) =
      v * ∏ j, table j (l j) (r j) := by
    by_cases h : ∀ j, pathCompatible (c (prev j)) (l j) (r j) (c (nextCopy j))
    · simp [table, h, Finset.prod_mul_distrib, mul_assoc]
    · obtain ⟨j, hj⟩ := not_forall.mp h
      rw [ite_eq_right h, Finset.prod_eq_zero (Finset.mem_univ j) (by simp [table, hj]), mul_zero]
  simp_rw [factor, ← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ l : Links d → Bool, ∏ j, ∑ b : Bool, table j (l j) b := by
      apply Finset.sum_congr rfl
      intro l _
      exact (Fintype.prod_sum (fun j b => table j (l j) b)).symm
    _ = ∏ j : Links d, ∑ a : Bool, ∑ b : Bool, table j a b :=
      (Fintype.prod_sum (fun j a => ∑ b : Bool, table j a b)).symm
    _ = _ := Finset.prod_congr rfl fun j _ => signed_path _ _

/-- The signed internal vertices contract every even path chain to a single
bit, leaving an arbitrary remaining factor on the copies. -/
theorem contract_paths [Fintype V] (d : V → ℕ) (F : (Copies d → Bool) → R) :
    (∑ c : Copies d → Bool, ∑ l : Links d → Bool, ∑ r : Links d → Bool,
      if ∀ j, pathCompatible (c (prev j)) (l j) (r j) (c (nextCopy j)) then
        F c * (∏ j, signWeight (l j)) * ∏ j, signWeight (r j) else 0) =
    ∑ x : V → Bool, F (fun j => x j.1) := by
  simp_rw [contraction_at_copy]
  let fill (x : V → Bool) (j : Copies d) := x j.1
  symm
  apply Fintype.sum_of_injective fill
  · intro x y he
    funext v
    exact congrFun he ⟨v, 0⟩
  · intro c hc
    have hbad : ¬ ∀ j : Links d, c (prev j) = c (nextCopy j) := by
      intro hagree
      apply hc
      refine ⟨fun v => c ⟨v, 0⟩, ?_⟩
      funext ⟨v, i⟩
      exact Fin.inductionOn i rfl fun j ih => ih.trans (hagree ⟨v,j⟩)
    obtain ⟨j, hj⟩ := not_forall.mp hbad
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro x
    simp only [fill, prev, nextCopy, ite_true]
    rw [Fintype.prod_sigma]
    have heven (v : V) : (∏ _i : Fin (2 * d v), if x v then (1 : R) else -1) = 1 := by
      cases hx : x v <;> simp [pow_mul]
    change _ = F (fun j => x j.1) * ∏ v : V, ∏ _i : Fin (2 * d v), if x v then (1 : R) else -1
    rw [Finset.prod_eq_one (fun i _ => heven i), mul_one]

end IndependentSetCubic

end

end SpectralBooks
end LinearAlgebra
end OAI

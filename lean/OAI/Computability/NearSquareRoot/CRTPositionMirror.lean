import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Finset.Max

/-! # Cycle reflections obtained by a finite forward scan

The least position on a permutation orbit is reached within the first `k`
steps. If it is first reached from `x` in `t` steps, applying `t` more
steps gives the reflection of `x` about that least position.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

variable {k : ℕ} (p : Equiv.Perm (Fin k))

private def orbitWindow (x : Fin k) : Finset (Fin k) :=
  Finset.univ.image fun j : Fin (k+1) => (p^j.val) x

private theorem window_nonempty (x : Fin k) : (orbitWindow p x).Nonempty :=
  ⟨x, Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩

/-- Minimum seen on the bounded forward traversal of the orbit of `x`. -/
def orbitMin (x : Fin k) : Fin k := (orbitWindow p x).min' (window_nonempty p x)

private theorem min_in_window (x : Fin k) : orbitMin p x ∈ orbitWindow p x :=
  Finset.min'_mem _ _

theorem orbitMin_le_power (x : Fin k) (j : Fin (k+1)) : orbitMin p x ≤ (p^j.val) x :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)

theorem orbitMin_hit (x : Fin k) : ∃ j ≤ k, (p^j) x = orbitMin p x := by
  obtain ⟨j,_,e⟩ := Finset.mem_image.mp (min_in_window p x)
  exact ⟨j.val, Nat.le_of_lt_succ j.isLt, e⟩

private def hits (x : Fin k) : Finset (Fin (k+1)) :=
  Finset.univ.filter fun j => (p^j.val) x = orbitMin p x

private theorem hits_nonempty (x : Fin k) : (hits p x).Nonempty := by
  obtain ⟨j,h,e⟩ := orbitMin_hit p x
  exact ⟨⟨j,Nat.lt_succ_of_le h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩⟩

/-- First step at which the least orbit position occurs. -/
def orbitTime (x : Fin k) : Fin (k+1) := (hits p x).min' (hits_nonempty p x)

theorem orbitTime_spec (x : Fin k) : (p^(orbitTime p x).val) x = orbitMin p x :=
  (Finset.mem_filter.mp (Finset.min'_mem (hits p x) (hits_nonempty p x))).2

private theorem mem_window {x y : Fin k} : y ∈ orbitWindow p x ↔ p.SameCycle x y := by
  classical
  constructor
  · rintro hy
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    exact Equiv.Perm.sameCycle_pow_right.mpr Equiv.Perm.SameCycle.rfl
  · intro h
    let orbit := Finset.univ.filter (p.SameCycle x)
    have mem (z : Fin k) : z ∈ orbit ↔ p.SameCycle x z := by simp [orbit]
    have cyc : p.IsCycleOn (orbit : Set (Fin k)) := by
      refine ⟨p.bijOn (fun z => ?_), fun a ha b hb => ((mem a).mp ha).symm.trans ((mem b).mp hb)⟩
      change p z ∈ orbit ↔ z ∈ orbit
      rw [mem,mem,Equiv.Perm.sameCycle_apply_right]
    obtain ⟨j,hj,hit⟩ := cyc.exists_pow_eq ((mem x).mpr Equiv.Perm.SameCycle.rfl) ((mem y).mpr h)
    have bounded : orbit.card ≤ k := (Finset.card_le_univ orbit).trans_eq (Fintype.card_fin k)
    exact Finset.mem_image.mpr ⟨⟨j,by omega⟩,Finset.mem_univ _,hit⟩

theorem orbitMin_eq {x y : Fin k} (h : p.SameCycle x y) : orbitMin p x = orbitMin p y := by
  have eq : orbitWindow p x = orbitWindow p y := by
    ext z
    rw [mem_window,mem_window]
    exact ⟨h.symm.trans, h.trans⟩
  unfold orbitMin
  congr 1

/-- Reflect about the canonical minimum using only positive powers of the input table. -/
def forwardMirror (x : Fin k) : Fin k := (p^(orbitTime p x).val) (orbitMin p x)

/-- Any visit time to the minimum gives the same reflected position. -/
theorem forwardMirror_of_power (x : Fin k) (j : ℕ) (h : (p^j) x = orbitMin p x) :
    forwardMirror p x = (p^j) (orbitMin p x) := by
  change (p^(orbitTime p x).val) _ = _
  conv_lhs => rw [← h]
  conv_rhs => rw [← orbitTime_spec p x]
  simpa only [zpow_natCast] using p.zpow_apply_comm (orbitTime p x).val (j : ℤ) (x := x)

private theorem join_exponents (j t : ℤ) (x : Fin k) : (p^j) ((p^t) x) = (p^(j+t)) x := by
  rw [zpow_add]
  rfl

private theorem mirror_at_power (x : Fin k) (j : ℤ) :
    forwardMirror p ((p^j) (orbitMin p x)) = (p^(-j)) (orbitMin p x) := by
  let b := orbitMin p x
  let y := (p^j) b
  have same : p.SameCycle x y := Equiv.Perm.sameCycle_zpow_right.mpr ((mem_window p).mp (min_in_window p x))
  have base : orbitMin p y = b := (orbitMin_eq p same).symm
  have hit := orbitTime_spec p y
  rw [base] at hit
  change (p^(orbitTime p y).val) (orbitMin p y) = (p^(-j)) b
  rw [base]
  apply (p^j).injective
  rw [join_exponents, add_neg_cancel, zpow_zero, Equiv.Perm.one_apply]
  rw [← zpow_natCast, p.zpow_apply_comm j (orbitTime p y).val]
  exact hit

private theorem return_to_start (x : Fin k) :
    (p^(-(orbitTime p x).val : ℤ)) (orbitMin p x) = x := by
  rw [← orbitTime_spec p x, ← zpow_natCast, join_exponents, neg_add_cancel, zpow_zero]
  rfl

theorem forwardMirror_involutive : Function.Involutive (forwardMirror p) := by
  intro x
  have e : forwardMirror p x = (p^((orbitTime p x).val : ℤ)) (orbitMin p x) := by
    simp only [forwardMirror, zpow_natCast]
  rw [e, mirror_at_power, return_to_start]

theorem shiftedMirror_involutive : Function.Involutive (p ∘ forwardMirror p) := by
  intro x
  simp only [Function.comp_apply]
  let j : ℤ := (orbitTime p x).val
  have shift (n : ℤ) (b : Fin k) : p ((p^n) b) = (p^(1+n)) b := by
    rw [← join_exponents, zpow_one]
  have e : p (forwardMirror p x) = (p^(1+j)) (orbitMin p x) := by
    rw [← shift]
    simp only [forwardMirror, j, zpow_natCast]
  rw [e, mirror_at_power, shift, show 1 + -(1+j) = -j by omega, return_to_start]

/-- The canonical reflections can be composed to implement the input permutation. -/
theorem forwardMirror_factor :
    let a : Equiv.Perm (Fin k) := ⟨forwardMirror p, forwardMirror p,
      forwardMirror_involutive p, forwardMirror_involutive p⟩
    let b : Equiv.Perm (Fin k) := ⟨p ∘ forwardMirror p, p ∘ forwardMirror p,
      shiftedMirror_involutive p, shiftedMirror_involutive p⟩
    a.trans b = p := by
  apply Equiv.ext
  intro x
  exact congrArg p (forwardMirror_involutive p x)

end Controlled

end NearSquareRoot
end Computability
end OAI

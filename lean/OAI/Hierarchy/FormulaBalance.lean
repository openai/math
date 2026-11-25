import OAI.Hierarchy.FormulaDepth
import OAI.Hierarchy.FormulaSeparator
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Brent balancing for commutative arithmetic formulas

A balanced subtree is computed recursively, together with the two specializations
of its one-hole context at zero and one. Combining these three results adds
three binary gates along the longest path. Two rounds suffice to halve the
gate-count budget up to an additive constant.
-/

namespace Hierarchy.Formula

open MatrixMultiplication.Arithmetic

universe u
variable {F : Type u} [Field F] {σ : Type}

private abbrev BalancedAt (F : Type u) [Field F] (σ : Type) (n d : ℕ) : Prop :=
  ∀ f : Formula F σ, f.cost ≤ n → ∃ g : Formula F σ, g.polynomial = f.polynomial ∧ g.depth ≤ d

private theorem balance_step {n m d : ℕ} (shrink : 2 * n + 1 < 3 * (m + 1))
    (ih : BalancedAt F σ m d) : BalancedAt F σ n (d + 3) := by
  intro f bound
  by_cases small : f.cost < 2
  · exact ⟨f, rfl, by have := depth_le_cost f; omega⟩
  obtain ⟨h,z,o,eval,hs,zs,os⟩ := exists_separator f (by omega)
  obtain ⟨a,ha,da⟩ := ih h (by omega)
  obtain ⟨b,hb,db⟩ := ih z (by omega)
  obtain ⟨c,hc,dc⟩ := ih o (by omega)
  refine ⟨.add b (.mul a (.sub c b)), ?_, ?_⟩
  · change b.polynomial + a.polynomial * (c.polynomial - b.polynomial) = f.polynomial
    simpa only [ha,hb,hc] using eval.symm
  · change max b.depth (max a.depth (max c.depth b.depth + 1) + 1) + 1 ≤ d + 3
    omega

private theorem balanced_dyadic (t : ℕ) : BalancedAt F σ (2 ^ (t + 1) + 1) (6 * t + 3) := by
  induction t with
  | zero =>
    intro f bound
    exact ⟨f,rfl,(depth_le_cost f).trans bound⟩
  | succ t ih =>
    let b := 2 ^ (t + 1)
    let middle := (4 * b + 3) / 3
    have first := balance_step (F := F) (σ := σ) (n := middle) (m := b + 1)
      (by dsimp only [middle]; omega) ih
    have second := balance_step (n := 2 * b + 1) (m := middle)
      (by dsimp only [middle]; omega) first
    intro f bound
    have double : 2 ^ (t + 1 + 1) = 2 * b :=
      (pow_succ 2 (t + 1)).trans (Nat.mul_comm _ _)
    rw [double] at bound
    obtain ⟨g,eq,dep⟩ := second f bound
    exact ⟨g,eq,by omega⟩

/-- Every division-free formula has an equivalent formula of logarithmic depth.
The equality holds in the formal polynomial ring, over every field. -/
theorem exists_balanced (f : Formula F σ) :
    ∃ g : Formula F σ, g.polynomial = f.polynomial ∧
      g.depth ≤ 6 * Nat.log 2 (f.cost + 2) + 6 := by
  let t := Nat.log 2 (f.cost + 2)
  have lt : f.cost + 2 < 2 ^ (t + 1) :=
    (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega)).mp (Nat.lt_succ_self t)
  obtain ⟨g,hg,hd⟩ := balanced_dyadic (F := F) (σ := σ) t f (by omega)
  exact ⟨g,hg,hd.trans (by dsimp only [t]; omega)⟩

/-- The number of binary paths at the logarithmic depth bound is polynomial. -/
theorem pow_le_of_log_depth {h n : ℕ} (hn : 2 ≤ n) (depth : h ≤ 6 * Nat.log 2 n + 6) :
    2 ^ h ≤ n ^ 12 := by
  have hpow := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  calc
    2 ^ h ≤ 2 ^ (6 * Nat.log 2 n + 6) := Nat.pow_le_pow_right (by decide) depth
    _ = (2 ^ Nat.log 2 n) ^ 6 * 2 ^ 6 := by rw [pow_add, Nat.mul_comm 6, pow_mul]
    _ ≤ n ^ 6 * n ^ 6 := Nat.mul_le_mul (Nat.pow_le_pow_left hpow _) (Nat.pow_le_pow_left hn _)
    _ = n ^ 12 := (pow_add n 6 6).symm

/-- The logarithmic-depth formula can simultaneously be chosen with polynomial size. -/
theorem exists_balanced_cost (f : Formula F σ) :
    ∃ g : Formula F σ, g.polynomial = f.polynomial ∧
      g.depth ≤ 6 * Nat.log 2 (f.cost + 2) + 6 ∧ g.cost ≤ (f.cost + 2) ^ 12 := by
  obtain ⟨g,hg,hd⟩ := exists_balanced f
  refine ⟨g,hg,hd,?_⟩
  exact ((Nat.le_succ _).trans (cost_succ_le_pow_depth g)).trans (pow_le_of_log_depth (by omega) hd)

end Hierarchy.Formula

end OAI

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace OAI
/-! # Round-robin allocation of the factors in one resource class -/

namespace Hierarchy.RoundRobin

open scoped BigOperators

/-- An item at position j in a class goes to tick j modulo the number of ticks. -/
def selected (n T : ℕ) (tick : Fin T) : Finset ℕ :=
  (Finset.range n).filter (· ≡ tick.val [MOD T])

theorem scheduled_once (n T : ℕ) (positive : 0<T) (i : ℕ) (inside : i<n) :
    ∃! t : Fin T, i ∈ selected n T t := by
  let t : Fin T := ⟨i%T, Nat.mod_lt i positive⟩
  have iff_slot (z : Fin T) : i ∈ selected n T z ↔ t=z := by
    simp only [selected, Finset.mem_filter, Finset.mem_range, inside, true_and,
      Nat.ModEq, Nat.mod_eq_of_lt z.isLt, Fin.ext_iff]
    rfl
  exact ⟨t, (iff_slot t).mpr rfl, fun z hz=>((iff_slot z).mp hz).symm⟩

/-- Summing the assigned weights over all ticks counts each list position once. -/
theorem sum_selected (n T : ℕ) (positive : 0<T) (cost : ℕ → ℝ) :
    (∑ t : Fin T, ∑ i∈selected n T t, cost i) = ∑ i∈Finset.range n, cost i := by
  classical
  let slot (i : ℕ) : Fin T := ⟨i%T,Nat.mod_lt _ positive⟩
  have test (t : Fin T) (i : ℕ) : i ≡ t.val [MOD T] ↔ slot i=t := by
    rw [Nat.ModEq,Nat.mod_eq_of_lt t.isLt,Fin.ext_iff]
  simp only [selected,Finset.sum_filter,test]
  rw [Finset.sum_comm]
  simp

theorem count_bounds (n T : ℕ) (tick : Fin T) :
    (n:ℝ)/T - 1 ≤ ((selected n T tick).card:ℝ) ∧
    ((selected n T tick).card:ℝ) ≤ (n:ℝ)/T + 1 := by
  have hp : 0<T := Nat.zero_lt_of_lt tick.isLt
  have pos : 0<(T:ℝ) := by exact_mod_cast hp
  have eqn : (selected n T tick).card = n/T + if tick.val%T < n%T then 1 else 0 := by
    rw [selected, ←Nat.count_eq_card_filter_range, Nat.count_modEq_card n hp tick.val]
  have counts : n/T ≤ (selected n T tick).card ∧ (selected n T tick).card ≤ n/T+1 := by
    rw [eqn]
    split <;> omega
  have lo : ((n/T:ℕ):ℝ) ≤ (n:ℝ)/T := by
    apply (le_div_iff₀ pos).2
    exact_mod_cast Nat.div_mul_le_self n T
  have hi : (n:ℝ)/T ≤ ((n/T:ℕ):ℝ)+1 := by
    apply (div_le_iff₀ pos).2
    have remainder := Nat.mod_add_div n T
    have hm := Nat.mod_lt n hp
    have bound : n ≤ (n/T+1)*T := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (n/T)];omega
    exact_mod_cast bound
  have a : ((n/T:ℕ):ℝ) ≤ (selected n T tick).card := by exact_mod_cast counts.1
  have z : ((selected n T tick).card:ℝ) ≤ ((n/T:ℕ):ℝ)+1 := by exact_mod_cast counts.2
  constructor <;> linarith

private theorem sum_bounds (s : Finset ℕ) (cost : ℕ → ℝ) {lo hi : ℝ}
    (bounds : ∀ i∈s, lo ≤ cost i ∧ cost i ≤ hi) :
    s.card*lo ≤ ∑ i∈s, cost i ∧ (∑ i∈s, cost i) ≤ s.card*hi := by
  constructor
  · simpa using Finset.sum_le_sum (s:=s) (g:=cost) (f:=fun _=>lo) (fun i hi=>(bounds i hi).1)
  · simpa using Finset.sum_le_sum (s:=s) (f:=cost) (g:=fun _=>hi) (fun i hi=>(bounds i hi).2)

/-- The per-coordinate bound in one geometric class. The error is an additive
single-item scale, independent of the number of factors in the class. -/
theorem load_bounds (n T : ℕ) (tick : Fin T) (cost : ℕ → ℝ) (lo b : ℝ)
    (nonneg : 0≤lo) (ratio : 0<b) (bounds : ∀ i<n, lo≤cost i ∧ cost i≤b*lo) :
    (∑ i∈Finset.range n, cost i)/((T:ℝ)*b) - lo ≤ ∑ i∈selected n T tick, cost i ∧
    (∑ i∈selected n T tick, cost i) ≤ b*((∑ i∈Finset.range n, cost i)/(T:ℝ))+b*lo := by
  have pos : 0<(T:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt tick.isLt
  have cnt := count_bounds n T tick
  have full := sum_bounds (Finset.range n) cost (fun i hi=>bounds i (Finset.mem_range.mp hi))
  rw [Finset.card_range] at full
  have part := sum_bounds (selected n T tick) cost (fun i hi=>
    bounds i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
  have upper : (∑ i∈Finset.range n, cost i)/((T:ℝ)*b) ≤ ((n:ℝ)/T)*lo := by
    apply (div_le_iff₀ (mul_pos pos ratio)).2
    convert full.2 using 1; field_simp
  have lower : ((n:ℝ)/T)*lo ≤ (∑ i∈Finset.range n, cost i)/(T:ℝ) := by
    apply (le_div_iff₀ pos).2
    convert full.1 using 1; field_simp
  constructor
  · have a := mul_le_mul_of_nonneg_right cnt.1 nonneg
    linarith only [upper, part.1, a, sub_mul ((n:ℝ)/T) 1 lo, one_mul lo]
  · have z := mul_le_mul_of_nonneg_right cnt.2 (mul_nonneg ratio.le nonneg)
    calc
      _ ≤ ((n:ℝ)/T+1)*(b*lo) := part.2.trans z
      _ = b*(((n:ℝ)/T)*lo)+b*lo := by ring
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left lower ratio.le) _

end Hierarchy.RoundRobin

end OAI

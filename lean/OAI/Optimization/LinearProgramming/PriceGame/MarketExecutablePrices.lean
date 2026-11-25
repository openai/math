import OAI.Optimization.LinearProgramming.PriceGame.MarketExistence
import Mathlib.Data.List.MinMax

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph
open Quiver

variable {E G : Type*}

/-- Effective enumeration of residual arcs when availability is decidable. -/
@[instance_reducible] def Graph.Network.enumEdges (n : Network E G)
    (dec : ∀ e i, Decidable (n.accepts e i)) (a b : Vertex n) : Fintype (a ⟶ b) := by
  letI : ∀ e i, Decidable (n.accepts e i) := dec
  letI decOption (e : E) (o : Option G) : Decidable (eligible n.accepts e o) := by
    cases o with
    | none => exact isTrue True.intro
    | some i => exact dec e i
  letI : Decidable (n.Allowed a b) := by
    cases a <;> cases b <;> unfold Graph.Network.Allowed <;> infer_instance
  exact PLift.fintypeProp _

/-- Computable Bellman potentials on the market's residual graph. -/
def Graph.Network.computePotential [Fintype E] [Fintype G] (n : Network E G)
    (dec : ∀ e i, Decidable (n.accepts e i)) : Vertex n → ℚ :=
  letI : ∀ a b : Vertex n, Fintype (a ⟶ b) := n.enumEdges dec
  Potentials.potential n.weight 0

theorem Graph.Network.computePotential_spec [Fintype E] [Fintype G] (n : Network E G)
    (dec : ∀ e i, Decidable (n.accepts e i))
    {qty : E → ℕ} (hf : Optimum.Feasible n.pos qty n.accepts n.f)
    (hmax : ∀ f', Optimum.Feasible n.pos qty n.accepts f' → Optimum.value n.c f' ≤ Optimum.value n.c n.f) :
    ResidualPotentials n.pos n.accepts n.c n.f (fun e => n.computePotential dec (.expert e))
      (fun o => n.computePotential dec (.opt o)) := by
  let _ : ∀ a b : Vertex n, Fintype (a ⟶ b) := n.enumEdges dec
  exact n.residual_of_inequalities _ (n.supports_of_feasible hf) fun t =>
    Potentials.arc_le_potential_sub n.weight 0 (n.simple_circuits_of_optimal hf hmax) t

/-- Enumerate the outside option followed by the eligible goods. -/
def options {g : ℕ} (available : Fin g → Bool) : List (Option (Fin g)) :=
  none :: ((List.finRange g).filter available).map some

theorem mem_options {g : ℕ} (available : Fin g → Bool) (o : Option (Fin g)) :
    o ∈ options available ↔ o.elim True (fun i => available i = true) := by
  cases o <;> simp [options, List.mem_finRange]

/-- First maximizing option in the canonical enumeration; also works for an empty good set. -/
def best {g : ℕ} (available : Fin g → Bool) (u : Option (Fin g) → ℚ) : Option (Fin g) :=
  ((options available).argmax u).getD none

theorem best_mem_argmax {g : ℕ} (available : Fin g → Bool) (u : Option (Fin g) → ℚ) :
    best available u ∈ (options available).argmax u := by
  cases h : (options available).argmax u with
  | none =>
    have he := List.argmax_eq_none.mp h
    simp [options] at he
  | some i => simp [best, h]

theorem best_eligible {g : ℕ} (available : Fin g → Bool) (u : Option (Fin g) → ℚ) :
    (best available u).elim True (fun i => available i = true) :=
  (mem_options _ _).mp (List.argmax_mem (best_mem_argmax _ _))

theorem best_maximizes {g : ℕ} (available : Fin g → Bool) (u : Option (Fin g) → ℚ)
    (o : Option (Fin g)) (ha : o.elim True (fun i => available i = true)) :
    u o ≤ u (best available u) :=
  List.le_of_mem_argmax ((mem_options _ _).mpr ha) (best_mem_argmax _ _)

/-- Zero-weight rows still choose a maximizing option and thus have unit total.
Positive rows divide the integral flow by their common scaled supply. -/
def allocation {e g : ℕ} (pos : Fin e → Bool) (available : Fin e → Fin g → Bool)
    (c : Fin e → Fin g → ℚ) (y : Fin g → ℚ) (qty : Fin e → ℕ)
    (flow : Fin e → Option (Fin g) → ℕ) (k : Fin e) (o : Option (Fin g)) : ℚ :=
  if qty k = 0 then
    if o = best (available k) (score pos c y k) then 1 else 0
  else fraction flow qty k o

theorem allocation_nonnegative {e g : ℕ} (pos : Fin e → Bool)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ) (y : Fin g → ℚ)
    (qty : Fin e → ℕ) (flow : Fin e → Option (Fin g) → ℕ) (k : Fin e) (o : Option (Fin g)) :
    0 ≤ allocation pos available c y qty flow k o := by
  unfold allocation
  split
  · split <;> norm_num
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem allocation_mass {e g : ℕ} (pos : Fin e → Bool)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ) (y : Fin g → ℚ)
    {qty : Fin e → ℕ} {flow : Fin e → Option (Fin g) → ℕ}
    (hf : Optimum.Feasible pos qty (fun k i => available k i = true) flow)
    (L : Fin e → ℚ) {Q : ℕ} (hQ : 0 < Q) (hsize : ∀ k, (qty k : ℚ) = (Q : ℚ) * L k)
    (k : Fin e) (o : Option (Fin g)) :
    L k * allocation pos available c y qty flow k o = (flow k o : ℚ) / (Q : ℚ) := by
  by_cases hzero : qty k = 0
  · have hrow : flow k o = 0 := Nat.le_zero.mp (hzero ▸ hf.entry_le k o)
    have hn : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
    have hL : L k = 0 := by
      have he := hsize k
      rw [hzero, Nat.cast_zero, eq_comm, mul_eq_zero] at he
      exact he.resolve_left hn
    simp [hL, hrow]
  · simp only [allocation, ite_eq_right hzero, fraction]
    have hr : (qty k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hzero
    have hq : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
    field_simp
    rw [hsize]; ring

theorem balanced_allocation {e g : ℕ} (pos : Fin e → Bool) (L : Fin e → ℚ)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ)
    {qty : Fin e → ℕ} {flow : Fin e → Option (Fin g) → ℕ} (P : Fin e → ℚ)
    (π : Option (Fin g) → ℚ) {Q : ℕ} (hQ : 0 < Q)
    (hs : ∀ k, (qty k : ℚ) = (Q : ℚ) * L k)
    (hf : Optimum.Feasible pos qty (fun k i => available k i = true) flow)
    (hp : ResidualPotentials pos (fun k i => available k i = true) c flow P π) :
    Balanced pos L (fun k i => available k i = true) c (price π)
      (allocation pos available c (price π) qty flow) := by
  let y := price π
  have hu (k : Fin e) (o : Option (Fin g)) (hpos : 0 < fraction flow qty k o) :
      0 < flow k o := by
    by_contra! hz; simp [fraction, Nat.le_zero.mp hz] at hpos
  have hvalid (k : Fin e) (o : Option (Fin g)) (hh : 0 < flow k o) :
      eligible (fun k i => available k i = true) k o := by
    cases o with
    | none => exact True.intro
    | some i =>
      by_contra! he
      exact hh.ne' (hf.unavailable _ _ he)
  have cond (k : Fin e) (o : Option (Fin g)) :
      eligible (fun k i => available k i = true) k o ↔ o.elim True (fun i => available k i = true) := by
    cases o <;> rfl
  refine ⟨fun k o => allocation_nonnegative pos available c (price π) qty flow k o, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hz : qty k = 0
    · simp [allocation, hz]
    · simp only [allocation, ite_eq_right hz, fraction, ← Finset.sum_div, ← Nat.cast_sum, hf.row]
      exact div_self (Nat.cast_ne_zero.mpr hz)
  · intro k o ho
    by_cases hz : qty k = 0
    · have heq : o = best (available k) (score pos c (price π) k) := by
        by_contra hne; simp [allocation, hz, hne] at ho
      rw [heq]; exact (cond _ _).mpr (best_eligible ..)
    · simp only [allocation, ite_eq_right hz] at ho
      exact hvalid _ _ (hu _ _ ho)
  · intro k o ho o' ha ha'
    by_cases hz : qty k = 0
    · have heq : o = best (available k) (score pos c (price π) k) := by
        by_contra hne; simp [allocation, hz, hne] at ho
      rw [heq]; exact best_maximizes _ _ _ ((cond _ _).mp ha')
    · simp only [allocation, ite_eq_right hz] at ho
      rw [score_eq_of_used hp k o ha (hu _ _ ho)]
      exact score_le_of_residual hp k o' ha'
  · intro i
    calc
      _ = ∑ k, (side pos k * (flow k (some i) : ℚ)) / (Q : ℚ) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_right_comm, allocation_mass pos available c (price π) hf L hQ hs]
        ring
      _ = 0 := by rw [← Finset.sum_div, show ∑ k, side pos k * (flow k (some i) : ℚ) = 0 from hf.good i,
        zero_div]

end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

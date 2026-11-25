import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI
/-! # Finite metric energies for the graph of ports -/

namespace ThreeFlat.Expander

open Finset

variable {V W X : Type*} [Fintype V] [Fintype W]

/-- Uniform average on a finite type. -/
noncomputable def avg (f : V → ℝ) : ℝ := (∑ i, f i) / Fintype.card V

theorem avg_le {f g : V → ℝ} (h : ∀ i, f i ≤ g i) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (sum_le_sum fun i _ => h i) (Nat.cast_nonneg _)

theorem avg_nonneg {f : V → ℝ} (h : ∀ i, 0 ≤ f i) : 0 ≤ avg f :=
  div_nonneg (sum_nonneg fun i _ => h i) (Nat.cast_nonneg _)

theorem avg_add (f g : V → ℝ) : avg (fun v => f v + g v) = avg f + avg g := by
  simp [avg, sum_add_distrib, add_div]

theorem avg_mul (c : ℝ) (f : V → ℝ) : avg (fun v => c*f v) = c * avg f := by
  rw [avg, avg, ← mul_sum]
  ring

@[simp] theorem avg_const [Nonempty V] (c : ℝ) : avg (fun _ : V => c) = c := by
  have hv : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [avg, hv]

theorem avg_congr (f g : V → ℝ) (h : ∀ i, f i = g i) : avg f = avg g :=
  congrArg avg (funext h)

theorem avg_prod (f : V → W → ℝ) :
    avg (fun p : V × W => f p.1 p.2) = avg (fun a => avg (f a)) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, ← Finset.sum_div]
  ring

theorem avg_equiv (e : V ≃ W) (f : W → ℝ) : avg (f ∘ e) = avg f := by
  unfold avg
  simp only [Function.comp_apply]
  rw [Fintype.card_congr e, e.sum_comp]

variable [PseudoMetricSpace X]

/-- The mean squared edge length of a transition matrix at a placement. -/
noncomputable def energy (G : Matrix V V ℝ) (x : V → X) : ℝ :=
  avg (fun i => ∑ j, G i j * dist (x i) (x j)^2)

/-- The mean squared distance of two independent, uniformly random vertices. -/
noncomputable def variance (x : V → X) : ℝ := avg (fun i => avg (fun j => dist (x i) (x j)^2))

/-- A uniform quadratic Poincaré inequality into the indicated target. -/
def Bound (G : Matrix V V ℝ) (Y : Type*) [PseudoMetricSpace Y] (γ : ℝ) : Prop :=
  ∀ x : V → Y, variance x ≤ γ * energy G x

/-- The transition probabilities of a multigraph from oriented arc multiplicities. -/
noncomputable def transition (c : V → V → ℕ) (q : ℕ) : Matrix V V ℝ :=
  fun i j => (c i j : ℝ) / q

end ThreeFlat.Expander

end OAI

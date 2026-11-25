import OAI.Optimization.LinearProgramming.PriceGame.MarketGraph
import OAI.Optimization.LinearProgramming.PriceGame.MarketOptimum
import OAI.Optimization.LinearProgramming.PriceGame.MarketPotentials
import OAI.Optimization.LinearProgramming.PriceGame.MarketDenominator

/-! # Existence of rational balanced prices with prescribed denominators

A maximizing integral flow has no positive simple residual circuit. Bellman
potentials for this network certify prices and support every positive allocation
on a maximizing option. The existence result here makes no runtime assertion.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
open Quiver OAI.Optimization.LinearProgramming.PriceGame.Market.Graph
variable {E G : Type*}

namespace Graph.Network

variable (n : Network E G) [Fintype E] [Fintype G]

theorem simple_circuits_of_optimal {qty : E → ℕ} (hf : Optimum.Feasible n.pos qty n.accepts n.f)
    (hmax : ∀ f', Optimum.Feasible n.pos qty n.accepts f' → Optimum.value n.c f' ≤ Optimum.value n.c n.f) :
    Potentials.NonpositiveSimpleCircuits n.weight := by
  classical
  intro a b p t hn
  let q := p.cons t
  have hc : Optimum.Circulation n.pos n.accepts n.f (n.change q) := by
    refine ⟨n.capacity_of_nodup q ?_, ?_, ?_, ?_⟩
    · simpa [q, List.concat_eq_append] using hn
    · intro e i hi
      exact n.change_forbidden q e (some i) hi
    · intro e
      simpa using n.row_change q e
    · intro i
      simpa [Optimum.sign, side] using n.option_change q (some i)
  rw [← n.weight_change q]
  exact Optimum.residual_nonpositive hf n.c hmax hc

omit [Fintype E] [Fintype G] in
theorem supports_of_feasible {qty : E → ℕ} [Fintype E] [Fintype G]
    (hf : Optimum.Feasible n.pos qty n.accepts n.f) (e : E) (o : Option G)
    (hu : 0 < n.f e o) : eligible n.accepts e o := by
  cases o with
  | none => exact True.intro
  | some i =>
    by_contra! bad
    exact (Nat.ne_of_gt hu) (hf.unavailable e i bad)

omit [Fintype E] [Fintype G] in
theorem residual_of_inequalities (P : Vertex n → ℚ)
    (used : ∀ e o, 0 < n.f e o → eligible n.accepts e o)
    (bounds : ∀ {a b : Vertex n} (t : a ⟶ b), n.weight t ≤ P a - P b) :
    ResidualPotentials n.pos n.accepts n.c n.f (fun e => P (.expert e)) (fun o => P (.opt o)) := by
  constructor
  · intro e o ha
    cases hp : n.pos e with
    | true =>
      let t : Vertex.expert e ⟶ Vertex.opt o := ⟨ha, Or.inl hp⟩
      simpa [weight, side, hp] using bounds t
    | false =>
      let t : Vertex.opt o ⟶ Vertex.expert e := ⟨ha, Or.inl hp⟩
      have ht := bounds t
      simp [weight, side, hp] at ht ⊢
      linarith
  · intro e o hu
    have ha := used e o hu
    cases hp : n.pos e with
    | true =>
      let t : Vertex.opt o ⟶ Vertex.expert e := ⟨ha, Or.inr hu⟩
      have ht := bounds t
      simp [weight, side, hp] at ht ⊢
      linarith
    | false =>
      let t : Vertex.expert e ⟶ Vertex.opt o := ⟨ha, Or.inr hu⟩
      have ht := bounds t
      simp [weight, side, hp] at ht ⊢
      linarith

omit [Fintype E] [Fintype G] in
theorem weight_abs_le {C : ℚ} (hC : 0 ≤ C)
    (hb : ∀ e i, n.accepts e i → |n.c e i| ≤ C) {a b : Vertex n} (t : a ⟶ b) :
    |n.weight t| ≤ C := by
  have hbid (e : E) (o : Option G) (ha : eligible n.accepts e o) : |bid n.c e o| ≤ C := by
    cases o with
    | none => simpa [bid] using hC
    | some i => exact hb e i ha
  cases a <;> cases b
  · exact t.down.elim
  · rename_i e o
    cases hp : n.pos e <;> simpa [weight, side, hp] using hbid e o t.down.1
  · rename_i o e
    cases hp : n.pos e <;> simpa [weight, side, hp] using hbid e o t.down.1
  · exact t.down.elim

omit [Fintype E] [Fintype G] in
theorem weight_integral (D : ℕ) (hd : ∀ e i, n.accepts e i → ∃ z : ℤ, (D : ℚ) * n.c e i = z)
    {a b : Vertex n} (t : a ⟶ b) : ∃ z : ℤ, (D : ℚ) * n.weight t = z := by
  have hbid (e : E) (o : Option G) (ha : eligible n.accepts e o) :
      ∃ z : ℤ, (D : ℚ) * bid n.c e o = z := by
    cases o with
    | none => exact ⟨0, by simp [bid]⟩
    | some i => exact hd e i ha
  cases a <;> cases b
  · exact t.down.elim
  · rename_i e o
    obtain ⟨z, hz⟩ := hbid e o t.down.1
    cases hp : n.pos e
    · exact ⟨-z, by simp [weight, side, hp, hz]⟩
    · exact ⟨z, by simp [weight, side, hp, hz]⟩
  · rename_i o e
    obtain ⟨z, hz⟩ := hbid e o t.down.1
    cases hp : n.pos e
    · exact ⟨z, by simp [weight, side, hp, hz]⟩
    · exact ⟨-z, by simp [weight, side, hp, hz]⟩
  · exact t.down.elim

theorem card_vertices : Fintype.card (Vertex n) = Fintype.card E + Fintype.card G + 1 := by
  let f : Vertex n ≃ E ⊕ Option G :=
    { toFun := fun | .expert e => .inl e | .opt o => .inr o
      invFun := fun | .inl e => .expert e | .inr o => .opt o
      left_inv := by rintro (_|_) <;> rfl
      right_inv := by rintro (_|_) <;> rfl }
  simpa [Nat.add_assoc] using Fintype.card_congr f

end Graph.Network

/-- The mathematical output of the balanced-prices algorithm. Under a prescribed
supply denominator, all masses are integral multiples of its reciprocal. The
same output respects every common denominator and every upper bound of the bids. -/
theorem exists_balanced_of_scaled [Fintype E] [Fintype G]
    (pos : E → Bool) (L : E → ℚ) (accepts : E → G → Prop) (c : E → G → ℚ)
    (qty : E → ℕ) (Q : ℕ) (hQ : 0 < Q) (hq : ∀ e, 0 < qty e)
    (hs : ∀ e, (qty e : ℚ) = (Q : ℚ) * L e) :
    ∃ y f, Balanced pos L accepts c y f ∧
      (∀ e o, ∃ k : ℕ, L e * f e o = (k : ℚ) / (Q : ℚ)) ∧
      (∀ D : ℕ, (∀ e i, accepts e i → ∃ z : ℤ, (D : ℚ) * c e i = z) →
        ∀ i, ∃ z : ℤ, (D : ℚ) * y i = z) ∧
      (∀ C : ℚ, 0 ≤ C → (∀ e i, accepts e i → |c e i| ≤ C) →
        ∀ i, |y i| ≤ 2 * ((Fintype.card E + Fintype.card G + 1 : ℕ) : ℚ) * C) := by
  classical
  obtain ⟨counts, hf, hmax⟩ := Optimum.exists_maximum pos qty accepts c
  let n : Graph.Network E G := ⟨pos, accepts, c, counts⟩
  have hc : Potentials.NonpositiveSimpleCircuits n.weight := n.simple_circuits_of_optimal (qty := qty) hf hmax
  let P : Vertex n → ℚ := Potentials.potential n.weight 0
  have harr : ∀ {a b : Vertex n} (t : a ⟶ b), n.weight t ≤ P a - P b :=
    fun t => Potentials.arc_le_potential_sub n.weight 0 hc t
  let π : Option G → ℚ := fun o => P (.opt o)
  have hr := n.residual_of_inequalities P (n.supports_of_feasible hf) harr
  refine ⟨price π, fraction counts qty, ?_, ?_, ?_, ?_⟩
  · exact balanced_of_residual hQ hq hs hf.row (n.supports_of_feasible hf) hf.good hr
  · intro e o
    exact ⟨counts e o, scaled_fraction counts qty hQ hq hs e o⟩
  · intro D hd i
    apply price_denominator π D _ i
    intro o
    exact Potentials.potential_denominator n.weight D (n.weight_integral D hd) (.opt o)
  · intro C hC hb i
    have hh := Potentials.normalized_abs_le n.weight C hC (n.weight_abs_le hC hb)
      (Vertex.opt (some i)) (Vertex.opt none)
    simpa [price, π, P, Potentials.normalized, n.card_vertices] using hh

/-- Balanced maximizing allocations exist for every finite rational market. -/
theorem exists_balanced [Fintype E] [Fintype G] (pos : E → Bool) (L : E → ℚ)
    (hL : ∀ e, 0 < L e) (accepts : E → G → Prop) (c : E → G → ℚ) :
    ∃ y f, Balanced pos L accepts c y f := by
  let Q := Denominator.denominator L
  have hD (e : E) : (L e).den ∣ Q := Denominator.den_dvd_denominator L e
  have hQ : 0 < Q := Denominator.denominator_pos L
  let units (e : E) := Denominator.qty Q (L e)
  have hq (e : E) : 0 < units e := Denominator.qty_pos (hL e) hQ (hD e)
  have hs (e : E) : (units e : ℚ) = (Q : ℚ) * L e :=
    Denominator.cast_qty (hL e).le (hD e)
  obtain ⟨y, f, h, _⟩ := exists_balanced_of_scaled pos L accepts c units Q hQ hq hs
  exact ⟨y, f, h⟩

end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

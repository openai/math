import OAI.Optimization.LinearProgramming.PriceGame.MarketExecutablePrices
import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentSolver
import OAI.Optimization.LinearProgramming.PriceGame.MarketPotentialsCost

/-! # Deterministic balanced prices by binary-scaled transshipment

The solver processes the binary supplies from most significant to least significant.
After finding the integral optimum, a final table of bounded-length path weights
fixes prices of the required size independently of the intermediate potentials.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph

private def asNetwork {e g : ℕ} (pos : Fin e → Bool) (available : Fin e → Fin g → Bool)
    (c : Fin e → Fin g → ℚ) (flow : Fin e → Option (Fin g) → ℕ) : Network (Fin e) (Fin g) :=
  ⟨pos, fun k i => available k i = true, c, flow⟩

private def asNetworkDec {e g : ℕ} (pos : Fin e → Bool) (available : Fin e → Fin g → Bool)
    (c : Fin e → Fin g → ℚ) (flow : Fin e → Option (Fin g) → ℕ) (k : Fin e) (i : Fin g) :
    Decidable ((asNetwork pos available c flow).accepts k i) :=
  inferInstanceAs (Decidable (available k i = true))

/-- Build each residual adjacency row and every Bellman value once, then use
the materialized vector for all output prices. -/
private def cachedPotential {e g : ℕ} (n : Network (Fin e) (Fin g))
    (dec : ∀ k i, Decidable (n.accepts k i)) : Vertex n → ℚ :=
  let idx := Augment.vertexIndex n
  let rows := Potentials.Cost.prepare idx (Augment.outgoing n dec)
  let values := Potentials.Cost.computedPotential idx n.weight 0 rows
  Potentials.Cost.read idx values

private theorem cachedPotential_eq {e g : ℕ} (n : Network (Fin e) (Fin g))
    (dec : ∀ k i, Decidable (n.accepts k i)) (v : Vertex n) :
    cachedPotential n dec v = n.computePotential dec v := by
  let _ : ∀ a b : Vertex n, Fintype (a ⟶ b) := n.enumEdges dec
  let idx := Augment.vertexIndex n
  let rows := Potentials.Cost.prepare idx (Augment.outgoing n dec)
  have full : ∀ {a b : Vertex n} (h : a ⟶ b),
      (⟨b, h⟩ : Σ j, a ⟶ j) ∈ Potentials.Cost.outgoing idx rows a := by
    intro a b h
    simpa [rows] using Augment.mem_outgoing n dec h
  exact Potentials.Cost.computedPotential_correct idx n.weight 0 rows full v

def pricesFromFlow {e g : ℕ} (pos : Fin e → Bool) (available : Fin e → Fin g → Bool)
    (c : Fin e → Fin g → ℚ) (flow : Fin e → Option (Fin g) → ℕ) : Fin g → ℚ :=
  price fun o => cachedPotential (asNetwork pos available c flow) (asNetworkDec pos available c flow) (.opt o)

/-- Public residual network of the final canonical price computation. -/
abbrev residualNetwork {e g : ℕ} (pos : Fin e → Bool) (available : Fin e → Fin g → Bool)
    (c : Fin e → Fin g → ℚ) (flow : Fin e → Option (Fin g) → ℕ) : Network (Fin e) (Fin g) :=
  ⟨pos, fun k i => available k i = true, c, flow⟩

/-- Normalize the terminal-zero Bellman potential by the dummy option. -/
theorem pricesFromFlow_eq_potential {e g : ℕ} (pos : Fin e → Bool)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ)
    (flow : Fin e → Option (Fin g) → ℕ) (i : Fin g) :
    let n := residualNetwork pos available c flow
    let d (k : Fin e) (j : Fin g) : Decidable (n.accepts k j) :=
      inferInstanceAs (Decidable (available k j = true))
    pricesFromFlow pos available c flow i =
      n.computePotential d (.opt none) - n.computePotential d (.opt (some i)) := by
  simp only [pricesFromFlow, price, cachedPotential_eq]
  rfl

def outputFromFlow {e g : ℕ} (pos : Fin e → Bool) (qty : Fin e → ℕ)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ)
    (flow : Fin e → Option (Fin g) → ℕ) :
    (Fin g → ℚ) × (Fin e → Option (Fin g) → ℚ) :=
  let y := pricesFromFlow pos available c flow
  (y, allocation pos available c y qty flow)

/-- The scorer and allocations are correct for any computed maximizing integral
flow. Unit allocations for zero-mass experts are selected by actual finite argmax. -/
theorem outputFromFlow_spec {e g : ℕ} (pos : Fin e → Bool) (L : Fin e → ℚ)
    (qty : Fin e → ℕ) (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ)
    (flow : Fin e → Option (Fin g) → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hs : ∀ k, (qty k : ℚ) = (Q : ℚ) * L k)
    (hf : Optimum.Feasible pos qty (fun k i => available k i = true) flow)
    (hopt : ∀ f, Optimum.Feasible pos qty (fun k i => available k i = true) f →
        Optimum.value c f ≤ Optimum.value c flow) :
    let out := outputFromFlow pos qty available c flow
    Balanced pos L (fun k i => available k i = true) c out.1 out.2 ∧
      (∀ k o, L k * out.2 k o = (flow k o : ℚ) / (Q : ℚ)) ∧
      (∀ D : ℕ, (∀ k i, available k i = true → ∃ z : ℤ, (D : ℚ) * c k i = z) →
        ∀ i, ∃ z : ℤ, (D : ℚ) * out.1 i = z) ∧
      (∀ C : ℚ, 0 ≤ C → (∀ k i, available k i = true → |c k i| ≤ C) →
        ∀ i, |out.1 i| ≤ 2 * ((e + g + 1 : ℕ) : ℚ) * C) := by
  let n := asNetwork pos available c flow
  let d (k : Fin e) (i : Fin g) : Decidable (n.accepts k i) := asNetworkDec pos available c flow k i
  let _ : ∀ a b : Vertex n, Fintype (a ⟶ b) := n.enumEdges d
  have hp := n.computePotential_spec d (qty := qty) hf hopt
  let P := n.computePotential d
  let π (o : Option (Fin g)) := P (.opt o)
  have HY : pricesFromFlow pos available c flow = price π := by
    funext i
    simp only [pricesFromFlow, price, cachedPotential_eq]
    rfl
  simp only [outputFromFlow, HY]
  constructor
  · exact balanced_allocation pos L available c _ π hQ hs hf hp
  refine ⟨allocation_mass pos available c (price π) hf L hQ hs, ?_, ?_⟩
  · intro D hd i
    apply price_denominator π D _ i
    intro o
    exact Potentials.potential_denominator n.weight D (n.weight_integral D hd) (.opt o)
  · intro C hC hb i
    have hh := Potentials.normalized_abs_le n.weight C hC (n.weight_abs_le hC hb)
      (Vertex.opt (some i)) (Vertex.opt none)
    change |price π i| ≤ _
    simpa [price, π, P, Graph.Network.computePotential, Potentials.normalized, n.card_vertices] using hh

/-- Deterministic market computation using the prescribed integral unit. -/
def computeWithDenominator {e g : ℕ} (pos : Fin e → Bool) (L : Fin e → ℚ)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ) (Q : ℕ) :
    (Fin g → ℚ) × (Fin e → Option (Fin g) → ℚ) :=
  let qty k := Denominator.qty Q (L k)
  let I : Augment.Input e g := ⟨pos, available, c⟩
  outputFromFlow pos qty available c (I.solve qty).flow

/-- Deterministic market computation choosing the product of reduced denominators. -/
def compute {e g : ℕ} (pos : Fin e → Bool) (L : Fin e → ℚ)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ) :
    (Fin g → ℚ) × (Fin e → Option (Fin g) → ℚ) :=
  computeWithDenominator pos L available c (Denominator.denominator L)

theorem computeWithDenominator_spec {e g : ℕ} (pos : Fin e → Bool) (L : Fin e → ℚ)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ) (Q : ℕ) (hQ : 0 < Q)
    (hL : ∀ k, 0 ≤ L k) (hden : ∀ k, (L k).den ∣ Q) :
    let out := computeWithDenominator pos L available c Q
    Balanced pos L (fun k i => available k i = true) c out.1 out.2 ∧
      (∀ k o, ∃ amount : ℕ, L k * out.2 k o = (amount : ℚ) / (Q : ℚ)) ∧
      (∀ D : ℕ, (∀ k i, available k i = true → ∃ z : ℤ, (D : ℚ) * c k i = z) →
        ∀ i, ∃ z : ℤ, (D : ℚ) * out.1 i = z) ∧
      (∀ C : ℚ, 0 ≤ C → (∀ k i, available k i = true → |c k i| ≤ C) →
        ∀ i, |out.1 i| ≤ 2 * ((e + g + 1 : ℕ) : ℚ) * C) := by
  let qty (k : Fin e) := Denominator.qty Q (L k)
  let I : Augment.Input e g := ⟨pos, available, c⟩
  let f := (I.solve qty).flow
  have hf := (I.solve_spec qty).feasible
  have ho := I.solve_optimal qty
  obtain ⟨hb, ham, hd, hc⟩ := outputFromFlow_spec pos L qty available c f Q hQ
    (fun k => Denominator.cast_qty (hL k) (hden k)) hf ho
  exact ⟨hb, fun k o => ⟨f k o, ham k o⟩, hd, hc⟩

theorem compute_balanced {e g : ℕ} (pos : Fin e → Bool) (L : Fin e → ℚ)
    (available : Fin e → Fin g → Bool) (c : Fin e → Fin g → ℚ) (hL : ∀ k, 0 ≤ L k) :
    Balanced pos L (fun k i => available k i = true) c
      (compute pos L available c).1 (compute pos L available c).2 :=
  (computeWithDenominator_spec pos L available c (Denominator.denominator L)
    (Denominator.denominator_pos L) hL (Denominator.den_dvd_denominator L)).1

end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentSolver
import OAI.Optimization.LinearProgramming.PriceGame.MarketNumberBounds
import OAI.Optimization.LinearProgramming.PriceGame.MarketExistence

/-! # Intermediate values of binary-scaled market transshipment -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace NumberBounds
open Quiver
open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph
open OAI.Optimization.LinearProgramming.PriceGame.Market.Potentials
open OAI.Optimization.LinearProgramming.PriceGame.Market.Augment

variable {m g : ℕ}

/-- A common magnitude and a common rational grid for both banks of stored potentials. -/
structure DualBound (D : ℕ) (U : ℚ) (s : State m g) : Prop where
  expert_abs : ∀ e, |s.pe e| ≤ U
  option_abs : ∀ o, |s.po o| ≤ U
  expert_grid : ∀ e, OnGrid D (s.pe e)
  option_grid : ∀ o, OnGrid D (s.po o)

theorem initial_bound (I : Input m g) (D : ℕ) (hD : ∀ e i, OnGrid D (I.intercept e i)) :
    DualBound D (OptimumDual.costBound I.intercept) I.initial := by
  let C := OptimumDual.costBound I.intercept
  have hC : 0 ≤ C := OptimumDual.costBound_nonneg _
  have hcgrid : OnGrid D C := by
    let s := insert (0 : ℚ) (Finset.univ.image (fun ki : Fin m × Fin g => |I.intercept ki.1 ki.2|))
    have hmem : C ∈ s := Finset.max'_mem _ _
    rcases Finset.mem_insert.mp hmem with hz | ha
    · rw [hz]; exact grid_zero D
    · obtain ⟨⟨e,i⟩, _, he⟩ := Finset.mem_image.mp ha
      rw [← he]
      exact (hD e i).abs
  constructor <;> simp only [Input.initial, State.pe_pack, State.po_pack]
  · intro e
    cases hp : I.positive e <;> simp [side, hp, abs_of_nonneg (OptimumDual.costBound_nonneg _)]
  · intro o; simpa using hC
  · intro e
    cases hp : I.positive e
    · simpa [side, hp, C] using hcgrid.neg
    · simpa [side, hp, C] using hcgrid
  · intro o; exact grid_zero D

theorem double_bound {D : ℕ} {U : ℚ} {s : State m g} (h : DualBound D U s) :
    DualBound D U (Input.double s) := by
  constructor
  · simpa [Input.double] using h.expert_abs
  · simpa [Input.double] using h.option_abs
  · simpa [Input.double] using h.expert_grid
  · simpa [Input.double] using h.option_grid

private def endpointWeight (n : Network (Fin m) (Fin g)) : Vertex n → Vertex n → ℚ
  | .expert e, .opt o => side n.pos e * bid n.c e o
  | .opt o, .expert e => -(side n.pos e * bid n.c e o)
  | _, _ => 0

private theorem weight_eq_endpoints (n : Network (Fin m) (Fin g)) {a b : Vertex n} (e : a ⟶ b) :
    n.weight e = endpointWeight n a b := by
  cases a <;> cases b <;> rfl

/-- Dummy-arc rewards vanish in either sign orientation. -/
theorem direct_cost (n : Network (Fin m) (Fin g)) (i : Fin m) :
    (direct n i).toPath.addWeight n.weight = 0 := by
  simp only [Quiver.Hom.toPath, Quiver.Path.addWeight_cons, Quiver.Path.addWeight_nil,
    zero_add, weight_eq_endpoints]
  cases hp : n.pos i <;> simp [start, finish, hp, endpointWeight, bid]

private def networkDec (I : Input m g) (s : State m g) (e : Fin m) (j : Fin g) :
    Decidable ((I.network s).accepts e j) := inferInstanceAs (Decidable (I.accepts e j))

theorem unit_bound (I : Input m g) {s : State m g} {D : ℕ} {U C : ℚ}
    (hU : DualBound D U s) (hC : 0 ≤ C)
    (hc : ∀ k i, I.accepts k i → |I.intercept k i| ≤ C)
    (hd : ∀ k i, I.accepts k i → OnGrid D (I.intercept k i)) (i : Fin m) :
    DualBound D (U + (1 + ((m + g : ℕ) : ℚ) * C)) (I.unit s i) := by
  let n := I.network s
  let π := combine n s.pe s.po
  let dec (k : Fin m) (j : Fin g) : Decidable (n.accepts k j) := networkDec I s k j
  let q := route n dec π i
  let ref := (direct n i).toPath
  let r := targetReward n.weight π ref
  have hπ (v : Vertex n) : |π v| ≤ U := by
    cases v with
    | expert k => exact hU.expert_abs k
    | opt o => exact hU.option_abs o
  have hπD (v : Vertex n) : OnGrid D (π v) := by
    cases v with
    | expert k => exact hU.expert_grid k
    | opt o => exact hU.option_grid o
  have hsteps : Fintype.card (Vertex n) - 1 = m + g := by simp [n.card_vertices]
  have hu' (v : Vertex n) : |q.dual v| ≤ U + (1 + ((m + g : ℕ) : ℚ) * C) := by
    rw [show q.dual v = targetedPotential n.weight π ref v from route_dual n dec π i v]
    have hh := intermediate_abs n.weight hC (n.weight_abs_le hC hc) r
      (terminal_abs_of_direct n.weight π hπ ref (direct_cost n i)) (Fintype.card (Vertex n) - 1) v
    simpa [targetedPotential, potential, r, hsteps, add_comm, add_left_comm, add_assoc] using hh
  have hg' (v : Vertex n) : OnGrid D (q.dual v) := by
    rw [show q.dual v = targetedPotential n.weight π ref v from route_dual n dec π i v]
    exact intermediate_grid n.weight (n.weight_integral D hd) r
      (terminal_grid_of_direct n.weight π hπD ref (direct_cost n i)) _ v
  constructor <;> simp only [Input.unit, State.pe_pack, State.po_pack]
  · exact fun k => hu' (.expert k)
  · exact fun o => hu' (.opt o)
  · exact fun k => hg' (.expert k)
  · exact fun o => hg' (.opt o)

/-- This bound applies to an arbitrary prefix of the actual doubling/augmentation schedule. -/
theorem run_bound (I : Input m g) {D : ℕ} (hd : ∀ k i, OnGrid D (I.intercept k i))
    (l : List (Option (Fin m))) {s : State m g} {U : ℚ} (hs : DualBound D U s) :
    let C := OptimumDual.costBound I.intercept
    DualBound D (U + ((l.filterMap id).length : ℚ) * (1 + ((m + g : ℕ) : ℚ) * C))
      (l.foldl (operation Input.double I.unit) s) := by
  induction l generalizing s U with
  | nil => simpa using hs
  | cons a l ih =>
    cases a with
    | none => simpa [operation] using ih (double_bound hs)
    | some i =>
      have hu := unit_bound I hs (OptimumDual.costBound_nonneg _)
        (fun k j _ => OptimumDual.abs_le_costBound _ k j) (fun k j _ => hd k j) i
      have reorder (k a : ℚ) : U + (k + 1) * a = U + a + k * a := by ring
      change DualBound D (U + ((((l.filterMap id).length + 1 : ℕ) : ℚ) *
        (1 + ((m + g : ℕ) : ℚ) * OptimumDual.costBound I.intercept)))
        (l.foldl (operation Input.double I.unit) (I.unit s i))
      rw [Nat.cast_add, Nat.cast_one, reorder]
      exact ih hu

end NumberBounds
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

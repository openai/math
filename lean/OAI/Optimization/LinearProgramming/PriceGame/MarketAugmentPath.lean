import OAI.Optimization.LinearProgramming.PriceGame.MarketPotentials

/-! The finite-horizon Bellman potential for augmenting between prescribed endpoints. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment

open Quiver
open OAI.Optimization.LinearProgramming.PriceGame.Market.Potentials

variable {V : Type*} [Quiver V] (w : ∀ {u v : V}, (u ⟶ v) → ℚ)

/-- A feasible arc potential bounds every path by telescoping. -/
theorem path_le_drop {π : V → ℚ}
    (hπ : ∀ {u v : V} (a : u ⟶ v), w a ≤ π u - π v) {s t : V} (p : Path s t) :
    p.addWeight w ≤ π s - π t := by
  induction p with
  | nil => simp
  | cons p e ih => simp only [Path.addWeight_cons]; linarith only [ih, hπ e]

theorem nonpositive_of_potential {π : V → ℚ}
    (hπ : ∀ {u v : V} (a : u ⟶ v), w a ≤ π u - π v) : NonpositiveSimpleCircuits w := by
  intro u v p e _
  simpa using path_le_drop w hπ (p.cons e)

section Finite

variable [DecidableEq V] [Fintype V] [∀ i j : V, Fintype (i ⟶ j)]

/-- The payoff for finishing at the target exceeds the loss on a known path to it. -/
def targetReward (π : V → ℚ) {s t : V} (reference : Path s t) (v : V) : ℚ :=
  π v + if v = t then π s - π t - reference.addWeight w + 1 else 0

def targetedPotential (π : V → ℚ) {s t : V} (reference : Path s t) : V → ℚ :=
  potential w (targetReward w π reference)

/-- Every maximizing terminal-reward path from `s` ends at `t` and saturates its potential bound. -/
theorem target_attainment (π : V → ℚ)
    (hπ : ∀ {u v : V} (a : u ⟶ v), w a ≤ π u - π v) {s t : V} (reference : Path s t)
    {u : V} (p : Path s u)
    (hp : targetedPotential w π reference s = p.addWeight w + targetReward w π reference u) :
    u = t ∧ p.addWeight w = targetedPotential w π reference s - targetedPotential w π reference t := by
  let B := π s - π t - reference.addWeight w + 1
  let r := targetReward w π reference
  let q := potential w r
  have hc : NonpositiveSimpleCircuits w := nonpositive_of_potential w hπ
  have Bpos : 0 < B := by dsimp [B]; linarith [path_le_drop w hπ reference]
  have rt : r t = π t + B := by simp [r, B, targetReward]
  have qtarget : q t = π t + B := by
    obtain ⟨v, z, _, hz⟩ := potential_attained w r hc t
    have hl := path_le_drop w hπ z
    have hupper : r v ≤ π v + B := by
      by_cases h : v = t <;> simp [r, targetReward, h, B, Bpos.le]
    have hlower := walk_score_le_potential w r hc (Path.nil : Path t t)
    simp only [Path.addWeight_nil, zero_add, rt] at hlower
    exact le_antisymm (by change potential w r t ≤ _; linarith) hlower
  have forced : π s < q s := by
    have h := walk_score_le_potential w r hc reference
    rw [rt] at h
    dsimp [q, B] at *
    linarith only [h]
  change q s = p.addWeight w + r u at hp
  have hu : u = t := by
    by_contra ne
    have hu : r u = π u := by simp [r, targetReward, ne]
    rw [hu] at hp
    linarith only [path_le_drop w hπ p, hp, forced]
  refine ⟨hu, ?_⟩
  have rut : r u = π t + B := (congrArg r hu).trans rt
  rw [rut] at hp
  change p.addWeight w = q s - q t
  rw [qtarget, hp]; ring

/-- A maximum-weight simple augmenting path has zero slack under a feasible residual potential.
The target reward forces the bounded-horizon Bellman optimization to end at the requested sink. -/
theorem targeted_path (π : V → ℚ)
    (hπ : ∀ {u v : V} (a : u ⟶ v), w a ≤ π u - π v) {s t : V} (reference : Path s t) :
    (∀ {u v : V} (a : u ⟶ v), w a ≤ targetedPotential w π reference u -
        targetedPotential w π reference v) ∧
    ∃ p : Path s t, p.vertices.Nodup ∧ p.addWeight w = targetedPotential w π reference s -
        targetedPotential w π reference t := by
  have hc : NonpositiveSimpleCircuits w := nonpositive_of_potential w hπ
  refine ⟨fun a => arc_le_potential_sub w _ hc a, ?_⟩
  obtain ⟨u, p, simple, hp⟩ := potential_attained w (targetReward w π reference) hc s
  obtain ⟨rfl, tight⟩ := target_attainment w π hπ reference p hp
  exact ⟨p, simple, tight⟩

end Finite

/-- The same path is maximum even among walks with repetitions. -/
theorem optimal_of_tight {π : V → ℚ}
    (hπ : ∀ {u v : V} (a : u ⟶ v), w a ≤ π u - π v) {s t : V} (p : Path s t)
    (hp : p.addWeight w = π s - π t) (q : Path s t) : q.addWeight w ≤ p.addWeight w :=
  hp ▸ path_le_drop w hπ q

end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI

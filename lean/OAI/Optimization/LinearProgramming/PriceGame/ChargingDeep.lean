import OAI.Optimization.LinearProgramming.PriceGame.ChargingTransferSplit
import OAI.Optimization.LinearProgramming.PriceGame.ChargingInduction

/-! # Child-state charge on the fixed list of deeper experts -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset

/-- A child state's probability distribution induces a distribution on ambient
pivots from its active vertices. An absent or inactive pivot receives no mass. -/
theorem active_pivot_cap {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V)
    (m : V → ℚ) (μ : Option S → ℚ) (hμ : ∀ i : S, μ (some i) ≤ 32*m i) (i : V) :
    (∑ o : Option S, if o.map Subtype.val = some i then μ o else 0) ≤ 32*maskedMass S m i := by
  classical
  rw [Fintype.sum_option]
  simp only [Option.map_none, reduceCtorEq, ↓reduceIte, zero_add, Option.map_some, Option.some.injEq]
  by_cases hi : i ∈ S
  · let j : S := ⟨i,hi⟩
    have hf (z : S) : z.val = i ↔ z = j := ⟨fun hz => Subtype.ext (show z.val = j.val from hz), fun hz => congrArg Subtype.val hz⟩
    simp only [hf, sum_ite_eq', mem_univ, ↓reduceIte, maskedMass, hi]
    exact hμ j
  · have hn (z : S) : z.val ≠ i := fun hz => hi (hz ▸ z.property)
    simp [hn, maskedMass, hi]

/-- Pointwise transfer in the precise form needed by the failed-trial induction:
the probability is on `Option S`; skeletons and child prices are ambient. -/
theorem deepChildWeight_transfer {V : Type*} [Fintype V] [DecidableEq V] {d L : ℕ}
    (h : Bool) (S : Finset V) (m : V → ℚ) (hm : ∀ i, 0 ≤ m i)
    (U : Option S → Finset V) (hU : ∀ o, U o ⊆ S)
    (μ : Option S → ℚ) (hμ : ∀ o, 0 ≤ μ o) (hsum : ∑ o, μ o = 1)
    (hcap : ∀ i : S, μ (some i) ≤ 32 * m i) (a : DeeperSkeleton V d L) :
    weighted μ (fun o => childDeeperWeight (transitionMass h S (U o) m) (o.map Subtype.val) a) ≤
      8 * 16^(d+1) * deeperWeight (maskedMass S m) a :=
  reindexedWeight_transfer μ hμ hsum h S U hU m hm (fun o => o.map Subtype.val)
    (active_pivot_cap S m μ hcap) a.2.1 a.2.2

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI

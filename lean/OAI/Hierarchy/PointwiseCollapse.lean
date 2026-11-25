import OAI.Hierarchy.Catalyst
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI
/-! # The uniform form of the collapse theorem used by the diagonal -/

namespace Hierarchy.Catalyst

open ThreeFlat Filter
open scoped BigOperators Topology

/-- Independent copies receive disjoint data pins in their literal order. -/
def tickProduct {F : Type*} [Field F] {p : ℕ} (tick : BitNetwork F p) (q : ℕ)
    (bits : Fin (q*p) → Bool) : F :=
  ∏ j : Fin q, tick.eval (fun a => bits (finProdFinEquiv (j,a)))

/-- All ticks of the given size share the replication and gap envelopes. An
arbitrarily small power of the volume may be spent on replication, and an
arbitrarily small power may be lost from the gap. Both bounds hold before the
tick's choice of input length and instruction table. -/
def HasPointwiseCollapse (F : Type*) [Field F] (k : ℕ) : Prop :=
  ∀ᶠ A : ℕ in atTop, ∃ A' : ℕ, A < A' ∧ ∃ Q : ℕ → ℕ, ∃ D : ℕ → ℝ,
    (∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop,
      (Q w : ℝ) ≤ (2 : ℝ) ^ (ε * w) ∧ (2 : ℝ) ^ ((1-ε)*w) ≤ D w) ∧
    ∀ᶠ w : ℕ in atTop, ∀ (p : ℕ) (tick : BitNetwork F p),
      tick.cells + tick.internal + p ≤ 2^w → p*w^A' ≤ 2^w →
      ∃ q : ℕ, 0 < q ∧ q ≤ Q w ∧ ∃ X : Approximation F k (q*p),
        X.size * w^A ≤ q * 2^w ∧ X.PointwiseGap (tickProduct tick q) (D w)

end Hierarchy.Catalyst

end OAI

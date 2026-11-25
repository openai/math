import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Defs

/-!
# The two compression scales

A wide network counts stations and all their ports. A trivalent network
counts stations and exposed ports. Tables of arity above three must come
from a finite dictionary. The stages may use different dictionary limits
but must all work over the same field.
-/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

/-- Trivalent size of an exact tensor power with independent exterior bits. -/
def PowerSize {F : Type} [Field F] {a b : Wire} (k : Val a → Val b → F) (d m : ℕ) : Prop :=
  ∃ v, Net F (copies a d) (copies b d) (power k d) v ∧ m = v + d * (wd a + wd b)

/-- The conclusion of Theorem 2.1, uniformly in the starting network. -/
def Compresses (F : Type) [Field F] : Prop :=
  ∀ η : ℝ, 0 < η → ∃ γ : ℝ, 0 < γ ∧ ∀ κ : ℝ, 0 < κ →
    ∀ᶠ n : ℕ in atTop, ∀ (a b : Wire) (k : Val a → Val b → F) (v : ℕ),
      Net F a b k v →
      let e := wd a + wd b
      let m := v + e
      let h : ℝ := Nat.clog 2 n
      n ≤ e → (m : ℝ) ≤ (n : ℝ) ^ (21 / 20 : ℝ) →
      ∃ d m' : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (n : ℝ) ^ κ ∧ PowerSize k d m' ∧
        (m' : ℝ) ≤ d * ((m : ℝ) * h ^ (-γ) + (e : ℝ) * h ^ η)

/-- A station and port count with at most `B` distinct high-arity labels. -/
def Labeled {K : Type} [Field K] {a b : Wire} (k : Val a → Val b → K)
    (B s u : ℕ) : Prop :=
  ∃ L : Finset (Table K), L.card ≤ B ∧ Wide K u (↑L) a b k s

/-- One application of the table-network lemma in Section 5. -/
def ArityStep (K : Type) [Field K] (n B B' : ℕ) (b δ a ξ : ℝ) : Prop :=
  let h : ℝ := Nat.clog 2 n
  ∀ (x y : Wire) (k : Val x → Val y → K) (s u M : ℕ),
    Labeled k B s u → (u : ℝ) ≤ h ^ b →
    s ≤ M → n ≤ M → (M : ℝ) ≤ (n : ℝ) ^ (11 / 10 : ℝ) →
    ((wd x + wd y : ℕ) : ℝ) ≤ M * h ^ (-(2 * a)) →
    ∃ r s' u' : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ (n : ℝ) ^ ξ ∧
      Labeled (power k r) B' s' u' ∧
      (s' : ℝ) ≤ (M : ℝ) * r * h ^ (-((1 - δ) * a)) ∧
      (u' : ℝ) ≤ h ^ (b + (1 + δ) * a)

/-- Only finitely many arity exponents are needed for a fixed saving. The
field and label limits are chosen before the starting network. -/
def ArityReduction (F : Type) [Field F] : Prop :=
  ∀ δ β : ℝ, 0 < δ → δ ≤ 1 / 10 → 0 < β → β ≤ 1 / 2 →
    ∃ α : ℝ, 0 < α ∧ ∀ (a : ℝ) (J : ℕ), 0 < a → a < α → 0 < J →
      β + (1 + δ) * a * J ≤ 1 / 2 → ∀ ξ : ℝ, 0 < ξ → ∃ C : ℝ, 0 < C ∧
        ∀ᶠ n : ℕ in atTop, ∃ (K : Type) (_ : Field K) (_ : Algebra F K)
          (_ : Module.Finite F K) (B : ℕ → ℕ),
          (Module.finrank F K : ℝ) ≤ C * Real.log (Nat.clog 2 n) ∧
          ∀ j : ℕ, j < J → ArityStep K n (B j) (B (j + 1)) (β + (1 + δ) * a * j) δ a ξ

end OAI.LinearAlgebra.MatrixExponent

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds on independent lists

Here `P w t m` means that the `t`-fold tensor power at width `w` admits
an exact realization of size `m`. The three premises only use this family.
-/

namespace OAI.LinearAlgebra.MatrixExponent
open Filter

/-- A list contains `2^w` records, each with `2*w` bits. -/
def listBits (w : ℕ) : ℕ := 2 * w * 2 ^ w

def Seed (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ C : ℝ, ∀ᶠ w : ℕ in atTop, ∃ m : ℕ,
    P w 1 m ∧ (m : ℝ) ≤ C * listBits w * (w : ℝ) ^ 2

def ManyList (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
    1 ≤ t → t ≤ listBits w → P w t m →
    (t : ℝ) * listBits w * (w : ℝ) ^ σ < 3 * m

def Compression (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ γ : ℝ, 0 < γ ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ, 1 ≤ t → P w t m →
    (m : ℝ) ≤ (listBits w : ℝ) ^ (21 / 20 : ℝ) →
    ∃ d m' : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (listBits w : ℝ) ^ δ ∧
      P w (t * d) m' ∧
      let h : ℝ := Nat.clog 2 (listBits w)
      (m' : ℝ) ≤ d * ((m : ℝ) * h ^ (-γ) + t * (listBits w : ℝ) * h ^ η)

end OAI.LinearAlgebra.MatrixExponent

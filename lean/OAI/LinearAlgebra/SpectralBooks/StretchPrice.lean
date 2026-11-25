import OAI.LinearAlgebra.SpectralBooks.PermutationStretch
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Log prices on tensor coefficients at the sites of the stretch

An evaluation on restriction classes can be read on any finite set of local
coordinates. We record the monotonicity and finite ordinary-sum laws of this
coordinate evaluation for use in selecting one common summand.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped Classical BigOperators

section

/-- The coordinate evaluation of a price on the sites `u`, `B`, `C`. The
ordinary-sum coefficient is the log price of a binary diagonal on these sites.
At the zero tensor the conventional extension of a nonnegative log price is zero. -/
structure SitePriceEval (K : Type*) [CommSemiring K] (B C : Type) [Fintype B] [Fintype C] where
  value : {U : Type} → {X : B → Type} → {Y : C → Type} → [Fintype U] →
    [∀ b, Fintype (X b)] → [∀ c, Fintype (Y c)] → Tensor K U (∀ b, X b) (∀ c, Y c) → ℝ
  mono : ∀ {U U' : Type} {X X' : B → Type} {Y Y' : C → Type}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    [Fintype U'] [∀ b, Fintype (X' b)] [∀ c, Fintype (Y' c)]
    {T : Tensor K U (∀ b, X b) (∀ c, Y c)} {T' : Tensor K U' (∀ b, X' b) (∀ c, Y' c)},
    SiteRestriction T' T → value T' ≤ value T

/-- The ordinary-sum estimate on a fixed format; only the index set and the
coordinates vary. At an all-zero sum the extension by zero gives the same estimate. -/
def SitePriceEval.OrdinarySumBound {K : Type*} [CommSemiring K] {B C : Type} [Fintype B] [Fintype C]
    (p : SitePriceEval K B C) (D : ℝ) : Prop :=
  ∀ {L U : Type} {X : B → Type} {Y : C → Type}
    [Fintype L] [Nonempty L] [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : L → Tensor K U (∀ b, X b) (∀ c, Y c)), ∃ i,
      p.value (fun u x y => ∑ l, T l u x y) ≤ p.value (T i) + D * Real.logb 2 (Fintype.card L)

end

end SpectralBooks
end LinearAlgebra
end OAI

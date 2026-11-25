import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic

/-!
# Restriction after adjoining trivial legs

The embedding preserves products. A direct sum over the larger site
set gives each extra leg a block label. This costs an inequality in
one direction and permits independent closures in the other.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices

structure Padding {S T : Type*} [CommSemiring S] [CommSemiring T]
    [PartialOrder S] [PartialOrder T] (pad : S → T) : Prop where
  zero : pad 0 = 0
  one : pad 1 = 1
  le_iff (s t) : pad s ≤ pad t ↔ s ≤ t
  mul (s t) : pad (s * t) = pad s * pad t
  add_le (s t) : pad (s + t) ≤ pad s + pad t
  split {s x y} : pad s ≤ x + y → ∃ a b, pad a ≤ x ∧ pad b ≤ y ∧ s ≤ a + b
  factor {s a x} : pad s ≤ pad a * x → ∃ b, pad b ≤ x ∧ s ≤ a * b

end OAI.LinearAlgebra.MatrixExponent.Prices

import OAI.Computability.VPVNP.Diagonal
import OAI.Computability.VPVNP.PairCoefficient
import OAI.Computability.VPVNP.UniversalMachine

/-!
# The diagonal criterion for the explicit grammar and machine

In Proposition 9.1 the live sites run the clocked machine defining the
integer family. For each primed pair we use its actual universal grammar
label queries and count all joint parse choices with the nominated histogram.
The first-half gadget paths and the tail evaluator still have to realize
their specified path multiplicities within the program's budget.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace GrammarDiagonal

open MvPolynomial
open scoped Classical

variable {Cut Pair Site H A k : Type*} {Internal : Pair → Type*} {n m w : ℕ}
variable [Fintype Cut] [Fintype Pair] [DecidableEq Pair] [Fintype Site] [Fintype H]
variable [∀ i, Fintype (Internal i)] [Field k] [CommRing A] [Algebra k A]

/-- A nomination gives one fixed-width counter for every production label.
All possible counter settings are included. -/
abbrev Nomination (m n w : ℕ) (H : Type*) :=
  GrammarLabel (Fin m × Bool) H n → Fin (2 ^ w)

/-- The integer coefficient of the nominated histogram, counted by the pair
parser for the fixed incident exterior bits. -/
noncomputable def multiplicity {Bits : Type*} [Fintype Bits] (d : Fin n) (h : H)
    (x : Bits → Site → Fin m → Bool)
    (μ : Nomination m n w H) : ℕ :=
  Fintype.card {c : PairCoefficient.Choices H d x //
    ∀ a, PairCoefficient.jointHistogram d h x c a = (μ a).val}

variable {Path : Cut → Pair → Nomination m n w H → Type*}
variable [∀ ξ i μ, Fintype (Path ξ i μ)] [DecidableEq (GrammarLabel (Fin m × Bool) H n)]

/-- The two-mode simulation cannot coexist with the grammar label equations.
This is the finite algebraic part of Proposition 9.1 with the paper's site
counts, complete nomination ranges, and exact pair histogram multiplicities. -/
theorem noGrammarSimulation
    (d : Fin n) (h : H) (x : Cut → (i : Pair) → Internal i → Site → Fin m → Bool)
    (value : GrammarLabel (Fin m × Bool) H n → A)
    (heq : ∀ input, eval₂Hom (Int.castRingHom A) value (labelQuery d h input) = (acceptingCount input : A))
    (hfit : Fintype.card Site * (2 * d.val + 1) < 2 ^ w)
    (Φ : A →ₗ[k] k) (hunit : Φ 1 = 1)
    (gadget : ∀ ξ i μ, Path ξ i μ → A)
    (hsim : ∀ ξ i μ, ∑ q, gadget ξ i μ q = (multiplicity d h (x ξ i) μ : A))
    (tail : ∀ ξ (hs : Pair → Nomination m n w H), ((i : Pair) → Path ξ i (hs i)) → ℕ)
    (heval : ∀ ξ hs q, (tail ξ hs q : k) =
      Φ (∏ i, (∏ a, value a ^ (hs i a).val) * gadget ξ i (hs i) (q i))) :
    IsEmpty (Diagonal.OriginalPaths (fun ξ i s v => acceptingCount (x ξ i s v)) ≃
      Diagonal.LiveModes tail) := by
  refine Diagonal.noPairedChainSimulation (Path := Path) (Internal := Internal)
    (fun ξ i s v => acceptingCount (x ξ i s v)) (fun ξ i s v =>
    eval₂Hom (Int.castRingHom A) value (labelQuery d h (x ξ i s v))) Φ hunit
    (fun μ => ∏ a, value a ^ (μ a).val) (fun ξ i μ => multiplicity d h (x ξ i) μ)
    gadget tail (fun ξ i s v => heq (x ξ i s v)) ?_ hsim heval
  intro ξ i
  simpa only [multiplicity, PairCoefficient.jointPolynomial, map_sum, map_prod] using
    (PairCoefficient.evaluate_by_nominations d h (x ξ i) value w hfit).symm

end GrammarDiagonal

end VPVNP
end Computability
end OAI

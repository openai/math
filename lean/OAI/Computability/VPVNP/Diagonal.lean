import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# The paired-chain contraction in Proposition 9.1

`Cut` indexes all assignments to the exterior cuts of the primed pairs.
`Path ξ i μ` indexes the successful local paths for pair `i` at exterior
assignment `ξ` and nominated production histogram `μ`. The weights below
are the values of the corresponding label monomials in the coefficient algebra.

The algebraic argument uses linearity only after multiplying the weights of
all the pairs. The local simulation, equality with the original contraction,
and realization by the live program are explicit hypotheses of the criterion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Diagonal

open scoped BigOperators

variable {Cut Pair Hist A k : Type*}
variable [Fintype Cut] [Fintype Pair] [DecidableEq Pair] [Fintype Hist]
variable {Path : Cut → Pair → Hist → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]
variable [Field k] [CommRing A] [Algebra k A]

/-- Sum of the tail contributions over cuts, nominations, and local paths. -/
def evaluationMode
    (Φ : A →ₗ[k] k) (label : Hist → A)
    (gadget : ∀ ξ i μ, Path ξ i μ → A) : k :=
  ∑ ξ, ∑ h : Pair → Hist, ∑ q : (i : Pair) → Path ξ i (h i),
    Φ (∏ i, label (h i) * gadget ξ i (h i) (q i))

/-- Equation (9.5) evaluated in the coefficient algebra, using the
production coefficients in (9.4). -/
def primedContraction (label : Hist → A) (coeff : Cut → Pair → Hist → ℕ) : A :=
  ∑ ξ, ∏ i, ∑ μ, label μ * (coeff ξ i μ : A)

/-- Equation (9.2), with an assignment to the shared bits split into the
exterior cuts `ξ` and the internal bits `s i` of each pair. The sites in
pair `i` contribute the product of their integer path counts. -/
def originalContraction
    {Internal : Pair → Type*} [∀ i, Fintype (Internal i)] {Site : Type*} [Fintype Site]
    (paths : Cut → (i : Pair) → Internal i → Site → ℕ) : ℕ :=
  ∑ ξ, ∑ s : (i : Pair) → Internal i, ∏ i, ∏ v, paths ξ i (s i) v

/-- Replacing the site counts using (8.1) and expanding each pair by
(9.4) preserves the original contraction, as in (9.3) and (9.5). -/
theorem primedContraction_eq_original
    {Internal : Pair → Type*} [∀ i, Fintype (Internal i)] {Site : Type*} [Fintype Site]
    (paths : Cut → (i : Pair) → Internal i → Site → ℕ)
    (grammar : Cut → (i : Pair) → Internal i → Site → A)
    (label : Hist → A) (coeff : Cut → Pair → Hist → ℕ)
    (hsite : ∀ ξ i s v, grammar ξ i s v = (paths ξ i s v : A))
    (hexpand : ∀ ξ i, (∑ μ, label μ * (coeff ξ i μ : A)) =
      ∑ s, ∏ v, grammar ξ i s v) :
    primedContraction label coeff = (originalContraction paths : A) := by
  unfold primedContraction originalContraction
  simp_rw [hexpand, hsite, Fintype.prod_sum]
  push_cast
  rfl

/-- The weighted path identities for individual pairs determine the entire
evaluation-mode sum, even when the tail functional is not multiplicative. -/
theorem evaluationMode_eq
    (Φ : A →ₗ[k] k) (label : Hist → A) (coeff : Cut → Pair → Hist → ℕ)
    (gadget : ∀ ξ i μ, Path ξ i μ → A)
    (hsim : ∀ ξ i μ, ∑ q, gadget ξ i μ q = (coeff ξ i μ : A)) :
    evaluationMode Φ label gadget = Φ (primedContraction label coeff) := by
  unfold evaluationMode primedContraction
  simp only [← map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Fintype.prod_sum (fun i q => label (h i) * gadget ξ i (h i) q)]
  simp_rw [← Finset.mul_sum, hsim]

/-- The value of a label monomial with the given vector of exponents. -/
def labelMonomial {Label : Type*} [Fintype Label] (values : Label → A)
    (exponents : Label → ℕ) : A :=
  ∏ j, values j ^ exponents j

omit [DecidableEq Pair] in
/-- Adding the exponents along the chain produces the same element of the
coefficient algebra as multiplying the local label monomials. -/
theorem labelMonomial_accumulate {Label : Type*} [Fintype Label] (values : Label → A)
    (exponents : Pair → Label → ℕ) :
    labelMonomial values (fun j => ∑ i, exponents i j) =
      ∏ i, labelMonomial values (exponents i) := by
  unfold labelMonomial
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]

/-- Apply the evaluator to the accumulated exponents exactly once at the tail
of the chain. Its scalar contributions then sum to the evaluation-mode count. -/
theorem evaluationMode_accumulated
    {Production Gadget : Type*} [Fintype Production] [Fintype Gadget]
    (Φ : A →ₗ[k] k) (productionValues : Production → A) (κ : Gadget → A)
    (μ : Hist → Production → ℕ) (ν : ∀ ξ i h, Path ξ i h → Gadget → ℕ) :
    (∑ ξ, ∑ h : Pair → Hist, ∑ q : (i : Pair) → Path ξ i (h i),
      Φ (labelMonomial productionValues (fun j => ∑ i, μ (h i) j) *
        labelMonomial κ (fun j => ∑ i, ν ξ i (h i) (q i) j))) =
    evaluationMode Φ (fun h => labelMonomial productionValues (μ h))
      (fun ξ i h q => labelMonomial κ (ν ξ i h q)) := by
  unfold evaluationMode
  apply Finset.sum_congr rfl
  intro ξ _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro q _
  rw [labelMonomial_accumulate productionValues (fun i => μ (h i)),
    labelMonomial_accumulate κ (fun i => ν ξ i (h i) (q i)), Finset.prod_mul_distrib]

/-- Algebraic contradiction of Proposition 9.1. The count `Y` is the
original integer path count. The primed contraction represents that count
in `A`, while the live program counts one unit path plus evaluation mode
in `k`. Taking `k = ZMod p` gives the paper's contradiction modulo `p`. -/
theorem pairedChainCriterion
    (Y : ℕ) (Φ : A →ₗ[k] k) (hunit : Φ 1 = 1)
    (label : Hist → A) (coeff : Cut → Pair → Hist → ℕ)
    (gadget : ∀ ξ i μ, Path ξ i μ → A)
    (hsim : ∀ ξ i μ, ∑ q, gadget ξ i μ q = (coeff ξ i μ : A))
    (hprimed : primedContraction label coeff = (Y : A))
    (hlive : (Y : k) = 1 + evaluationMode Φ label gadget) : False := by
  have hscalar : Φ (Y : A) = (Y : k) := by
    calc
      Φ (Y : A) = Φ (Y • (1 : A)) := by rw [nsmul_one]
      _ = Y • (1 : k) := by rw [map_nsmul, hunit]
      _ = (Y : k) := nsmul_one Y
  rw [evaluationMode_eq Φ label coeff gadget hsim, hprimed, hscalar] at hlive
  exact one_ne_zero (add_right_cancel (hlive.symm.trans (zero_add (Y : k)).symm))

/-- The configurations counted by the original chain. For fixed cut bits and
internal bits, each site chooses one of its accepting paths independently. -/
abbrev OriginalPaths
    {Internal : Pair → Type*} {Site : Type*}
    (paths : Cut → (i : Pair) → Internal i → Site → ℕ) :=
  (ξ : Cut) × (s : (i : Pair) → Internal i) × ((i : Pair) → (v : Site) → Fin (paths ξ i (s i) v))

/-- The paths produced by the two live modes. In evaluation mode the tail
has a separate contribution for each sequence of branch choices. -/
abbrev LiveModes
    (tail : ∀ ξ (h : Pair → Hist), ((i : Pair) → Path ξ i (h i)) → ℕ) :=
  Unit ⊕ ((ξ : Cut) × (h : Pair → Hist) × (q : (i : Pair) → Path ξ i (h i)) × Fin (tail ξ h q))

/-- Proposition 9.1 in terms of the asserted path bijection, sitewise
coefficient equations, local weighted simulations, and tail path counts.
Canonical cut fields and padding in the live program ensure that its
evaluation mode has exactly the path multiplicities in `LiveModes`. -/
theorem noPairedChainSimulation
    {Internal : Pair → Type*} [∀ i, Fintype (Internal i)] {Site : Type*} [Fintype Site]
    (paths : Cut → (i : Pair) → Internal i → Site → ℕ)
    (grammar : Cut → (i : Pair) → Internal i → Site → A)
    (Φ : A →ₗ[k] k) (hunit : Φ 1 = 1)
    (label : Hist → A) (coeff : Cut → Pair → Hist → ℕ)
    (gadget : ∀ ξ i μ, Path ξ i μ → A)
    (tail : ∀ ξ (h : Pair → Hist), ((i : Pair) → Path ξ i (h i)) → ℕ)
    (hsite : ∀ ξ i s v, grammar ξ i s v = (paths ξ i s v : A))
    (hexpand : ∀ ξ i, (∑ μ, label μ * (coeff ξ i μ : A)) =
      ∑ s, ∏ v, grammar ξ i s v)
    (hsim : ∀ ξ i μ, ∑ q, gadget ξ i μ q = (coeff ξ i μ : A))
    (heval : ∀ ξ h q, (tail ξ h q : k) = Φ (∏ i, label (h i) * gadget ξ i (h i) (q i))) :
    IsEmpty (OriginalPaths paths ≃ LiveModes tail) := by
  classical
  constructor
  intro e
  apply pairedChainCriterion (originalContraction paths) Φ hunit label coeff gadget hsim
    (primedContraction_eq_original paths grammar label coeff hsite hexpand)
  have hcount : originalContraction paths = 1 + ∑ ξ, ∑ h, ∑ q, tail ξ h q := by
    simpa [OriginalPaths, LiveModes, originalContraction] using Fintype.card_congr e
  rw [hcount]
  simp [evaluationMode, heval]

end Diagonal

end VPVNP
end Computability
end OAI

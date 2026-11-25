import OAI.LinearAlgebra.SpectralBooks.GroundFieldComparison
import OAI.LinearAlgebra.SpectralBooks.CutSpectrum
import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum

/-!
# Selecting a normalized spectral point in a one-party extension

In the finite interpolation argument of the circuit dichotomy, a monomial
specifies old tensors and wires to a newly added party. Its prescribed log
value bounds the old log prices after contraction at that party. The bound is
sharp on the submonoid where the two wire multiplicities agree. This file
proves the separation step. The same spectral point realizes all the sharp
bounds and simultaneously respects the upper bounds on the other monomials.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators NNReal
noncomputable section

section

variable {M T : Type*} [AddCommMonoid M] [AddCommMonoid T]

/-- Pull expanded strict comparison back to formal products of generators.
The ordinary summands live in the target format and are bounded by local
linear images of the indicated products. -/
private theorem comparison_on_generators
    {E : Type*} (F : E → T →+ ℝ) (eval : M →+ T)
    {res : T → T → Prop} {ordinary : T → (L : ℕ) → (Fin L → T) → Prop}
    (h : ExpandedStrictComparison (Set.range F) res ordinary) :
    ExpandedStrictComparison (Set.range fun f ↦ (F f).comp eval) Eq
      (fun x L y ↦ ∃ z : Fin L → T, ordinary (eval x) L z ∧ ∀ l, res (z l) (eval (y l))) := by
  intro J x y hj cover
  obtain ⟨k, hk, hi⟩ := h (eval x) (eval ∘ y) hj (by
    rintro _ ⟨f,rfl⟩
    exact cover _ ⟨f, rfl⟩)
  refine ⟨k, hk, fun n hn ↦ ?_⟩
  obtain ⟨L, hL, hcount, z, hsum, words⟩ := hi n hn
  choose w hw using words
  refine ⟨L, hL, hcount, fun l ↦ ∑ t, y (w l t), ?_, fun l ↦ ⟨w l, rfl⟩⟩
  exact ⟨z, by simpa using hsum, fun l ↦ by simpa using hw l⟩

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nontrivial I] [Field K]

/-- Spectral interpolation from the contraction estimates. The hypothesis on
`cost` for ordinary sums is the old spectral point's direct-sum bound after
contracting the new party. In the interval interpolation application, `G`
contains the old tensors, the full diagonal, and the balanced two-wire supply. -/
theorem spectral_extension_of_contraction_bounds
    (eval : M →+ NonzeroProduct.{v} I K) (target : M →+ ℝ) (G : AddSubmonoid M)
    (cost : NonzeroProduct.{v} I K → ℝ)
    (hmono : ∀ {x y}, classOfProduct x ≤ classOfProduct y → cost x ≤ cost y)
    (upper : ∀ x, cost (eval x) ≤ target x)
    (sharp : ∀ x ∈ G, target x ≤ cost (eval x))
    (nneg : ∀ x, 0 ≤ target x)
    (cost_sum : ∀ (x L z), ClassOrdinarySum x L z →
      ∃ l, cost x ≤ cost (z l) + Real.logb 2 L)
    (u : M) (hu : u ∈ G) (h1 : target u = 1)
    (hu1 : ∀ f, logPoint.{v} (I := I) (K := K) f (eval u) = 1) :
    ∃ f, (∀ x, logPoint.{v} (I := I) (K := K) f (eval x) ≤ target x) ∧
      ∀ x ∈ G, logPoint f (eval x) = target x := by
  classical
  let E := normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)
  let : CompactSpace E := isCompact_iff_compactSpace.mp isCompact_spectrum
  let : Nonempty E := (spectrum_nonempty.{v} I K).to_subtype
  let F (f : E) : M →+ ℝ := (logPoint f).comp eval
  have cont (x : M) : Continuous (fun f ↦ F f x) :=
    continuous_spectralLogHom unit_le_nonzeroClass (eval x)
  have pos (f : E) (x : M) : 0 ≤ F f x := spectralLogHom_nonneg unit_le_nonzeroClass f _
  let ord (x : M) (L : ℕ) (y : Fin L → M) := ∃ z : Fin L → NonzeroProduct.{v} I K,
    ClassOrdinarySum (eval x) L z ∧ ∀ l, classOfProduct (z l) ≤ classOfProduct (eval (y l))
  have compare : ExpandedStrictComparison (Set.range F) Eq ord := @comparison_on_generators M (NonzeroProduct.{v} I K) _ _ E
    (logPoint (I := I) (K := K)) eval (fun x y ↦ classOfProduct x ≤ classOfProduct y)
    ClassOrdinarySum (expandedStrictComparison I K)
  obtain ⟨f, c, _, hle, heq⟩ := select_spectral_price_of_finite_comparison F target G 0 u
    cont pos nneg hu (h1 ▸ zero_lt_one) (fun f ↦ ⟨u, (hu1 f).symm ▸ zero_lt_one⟩) (by
      intro x hx J y cover
      obtain ⟨j, _⟩ := cover (Classical.choice inferInstance)
      refine finite_comparison_of_ordinary_sum (spectrum := Set.range F) (restricts := Eq)
        (ordinarySum := ord) (fun {j} ↦ @compare j) target (fun he ↦ (congrArg target he).le)
        (C := 1) zero_le_one ?_ (Fin.pos j) y ?_
      · intro n L Y _ hord
        obtain ⟨z, hsum, hz⟩ := hord
        obtain ⟨l, hl⟩ := cost_sum _ _ _ hsum
        have htarget := sharp (n • (0 + x)) (G.nsmul_mem (show 0 + x ∈ G by simpa) n)
        have hh := (hmono (hz l)).trans (upper _)
        exact ⟨l, by simpa only [one_mul] using htarget.trans (hl.trans (add_le_add_left hh _))⟩
      · rintro _ ⟨q, rfl⟩
        exact cover q)
  have hc : c = 1 := by
    have h := heq u hu
    change c * logPoint f (eval u) = target u at h
    simpa [hu1, h1] using h
  exact ⟨f, fun x ↦ by simpa [hc, F] using hle x, fun x hx ↦ by simpa [hc, F] using heq x hx⟩

end SiteTensor
end

end

end SpectralBooks
end LinearAlgebra
end OAI

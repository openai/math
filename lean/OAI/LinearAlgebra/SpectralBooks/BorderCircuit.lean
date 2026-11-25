import OAI.LinearAlgebra.SpectralBooks.FormalCircuit

/-!
# Degree-component border circuit size

The circuits are division-free straight-line programs with arbitrary fanout. Their scalar and
variable inputs are free, and each binary addition, subtraction or multiplication costs one.
Only coefficients of the specified total degree enter the affine space of the border model.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open Arithmetic MvPolynomial

variable {F σ ρ : Type*}

section PolynomialEvaluation

variable [CommRing F]

/-- Every formal polynomial occurs at an output register of a finite circuit. -/
theorem exists_registerPolynomial (f : MvPolynomial σ F) :
    ∃ (r : ℕ) (p : Program F σ r) (o : Fin r), registerPolynomial p o = f := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨1, Program.nil.step (.constant a), 0, rfl⟩
  | add f g hf hg =>
    obtain ⟨r, p, i, rfl⟩ := hf
    obtain ⟨s, q, j, rfl⟩ := hg
    refine ⟨_, (p.append q).step (.add (Program.oldIndex _ _ i) (Program.newIndex _ _ j)), 0, ?_⟩
    exact congrArg₂ (· + ·) (registerPolynomial_append_old p q i) (registerPolynomial_append_new p q j)
  | mul_X f j hf =>
    obtain ⟨r, p, i, rfl⟩ := hf
    exact ⟨_, (p.step (.input j)).step (.mul i.succ 0), 0, rfl⟩

end PolynomialEvaluation

variable [Field F]

/-- One coordinate for each monomial of total degree exactly `d`. -/
abbrev DegreeMonomial (σ : Type*) (d : ℕ) := {m : σ →₀ ℕ // m.degree = d}

/-- Coefficients of the degree-`d` homogeneous component in the monomial basis. -/
def degreeCoefficientVector {R : Type*} [CommSemiring R] (d : ℕ) (f : MvPolynomial σ R) :
    DegreeMonomial σ d → R :=
  fun m ↦ f.coeff m.val

@[simp] theorem degreeCoefficientVector_homogeneousComponent (d : ℕ) (f : MvPolynomial σ F) :
    degreeCoefficientVector d (homogeneousComponent d f) = degreeCoefficientVector d f := by
  funext m
  simp [degreeCoefficientVector, coeff_homogeneousComponent, m.property]

/-- Degree-`d` coefficient vectors of outputs with at most `s` arithmetic gates. -/
def circuitCoefficientVectors (F σ : Type*) [Field F] (d s : ℕ) : Set (DegreeMonomial σ d → F) :=
  {v | ∃ (r : ℕ) (p : Program F σ r) (o : Fin r),
    p.cost ≤ s ∧ degreeCoefficientVector d (registerPolynomial p o) = v}

/-- Membership in the Zariski closure of the degree-component circuit outputs over the algebraic
closure. This is the inequality `L̲_F^[d](f) ≤ s` for homogeneous `f`. -/
def DegreeBorderSizeAtMost (d s : ℕ) (f : MvPolynomial σ F) : Prop :=
  degreeCoefficientVector d (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) ∈
    zeroLocus (AlgebraicClosure F) (vanishingIdeal (AlgebraicClosure F)
      (circuitCoefficientVectors (AlgebraicClosure F) σ d s))

theorem DegreeBorderSizeAtMost.mono {d s t : ℕ} {f : MvPolynomial σ F}
    (h : DegreeBorderSizeAtMost d s f) (hst : s ≤ t) : DegreeBorderSizeAtMost d t f := by
  apply zeroLocus_anti_mono (vanishingIdeal_anti_mono ?_) h
  rintro v ⟨r, p, o, hp, hv⟩
  exact ⟨r, p, o, hp.trans hst, hv⟩

theorem exists_degreeBorderSizeAtMost (d : ℕ) (f : MvPolynomial σ F) :
    ∃ s, DegreeBorderSizeAtMost d s f := by
  obtain ⟨r, p, o, hp⟩ := exists_registerPolynomial
    (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f)
  refine ⟨p.cost, zeroLocus_vanishingIdeal_le _ ⟨r, p, o, le_rfl, ?_⟩⟩
  rw [hp]

/-- The least size of a circuit in the degree-component border model. -/
def degreeBorderSize (d : ℕ) (f : MvPolynomial σ F) : ℕ := by
  classical exact Nat.find (exists_degreeBorderSizeAtMost d f)

theorem degreeBorderSize_le_iff (d s : ℕ) (f : MvPolynomial σ F) :
    degreeBorderSize d f ≤ s ↔ DegreeBorderSizeAtMost d s f := by
  classical
  exact ⟨fun h ↦ (Nat.find_spec (exists_degreeBorderSizeAtMost d f)).mono h, Nat.find_min' (exists_degreeBorderSizeAtMost d f)⟩

/-- Lower bound with a real threshold, as used for the bound `2^(n^ε)`. -/
def DegreeBorderSizeAtLeast (d : ℕ) (b : ℝ) (f : MvPolynomial σ F) : Prop :=
  b ≤ (degreeBorderSize d f : ℝ)

theorem degreeBorderSizeAtLeast_iff (d : ℕ) (b : ℝ) (f : MvPolynomial σ F) :
    DegreeBorderSizeAtLeast d b f ↔ ∀ s : ℕ, DegreeBorderSizeAtMost d s f → b ≤ (s : ℝ) := by
  constructor
  · intro h s hs
    exact h.trans (by exact_mod_cast (degreeBorderSize_le_iff d s f).mpr hs)
  · intro h
    exact h _ ((degreeBorderSize_le_iff d _ f).mp le_rfl)

end

end

end SpectralBooks
end LinearAlgebra
end OAI

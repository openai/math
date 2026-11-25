import OAI.Computability.VPVNP.CircuitSize
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Nullstellensatz

/-!
# Degree-component border circuits

Section 2.1 takes the Zariski closure over the algebraic closure of the scalar field.
The coordinates of the ambient affine space record only the prescribed degree. Circuit
outputs before this projection may have arbitrary degree. The circuit size counts binary
gates and permits the use of any earlier gate as an operand.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial

/-- The exponent vectors indexing the coefficient space of a degree-`d` form. -/
def DegreeMonomial (σ : Type*) (d : ℕ) := {m : σ →₀ ℕ // m.degree = d}

instance {σ : Type*} [Finite σ] (d : ℕ) : Finite (DegreeMonomial σ d) :=
  Finsupp.finite_of_degree_eq d

/-- Projection from arbitrary formal polynomials to their degree-`d` coefficient vectors. -/
def coeffVector {σ K : Type*} [CommSemiring K] (d : ℕ) (p : MvPolynomial σ K) :
    DegreeMonomial σ d → K := fun i => p.coeff i.val

/-- Taking the homogeneous component first gives the same coefficient vector. -/
theorem coeffVector_homogeneousComponent {σ K : Type*} [CommSemiring K] (d : ℕ)
    (p : MvPolynomial σ K) : coeffVector d (homogeneousComponent d p) = coeffVector d p := by
  funext i
  simp only [coeffVector, coeff_homogeneousComponent, i.property, ite_true]

/-- Scalar extension on coefficient vectors is pointwise. -/
theorem coeffVector_map {σ K E : Type*} [CommSemiring K] [CommSemiring E] (d : ℕ)
    (h : K →+* E) (p : MvPolynomial σ K) :
    coeffVector d (map h p) = h ∘ coeffVector d p := by
  funext i
  exact coeff_map h _ _

/-- The affine Zariski closure, expressed as the common zero locus of all equations of a set. -/
def imageClosure {ι K : Type*} [Field K] (S : Set (ι → K)) : Set (ι → K) :=
  {x | ∀ q : MvPolynomial ι K, (∀ y ∈ S, eval y q = 0) → eval x q = 0}

/-- Agreement with the affine zero locus of the vanishing ideal. -/
theorem imageClosure_eq_zeroLocus {ι K : Type*} [Field K] (S : Set (ι → K)) :
    imageClosure S = zeroLocus K (vanishingIdeal K S) := rfl

/-- The set being approximated lies in its closure. -/
theorem subset_imageClosure {ι K : Type*} [Field K] (S : Set (ι → K)) : S ⊆ imageClosure S :=
  fun _ hx _ hq => hq _ hx

/-- Enlarging the set of attainable outputs enlarges its closure. -/
theorem imageClosure_mono {ι K : Type*} [Field K] {S T : Set (ι → K)} (h : S ⊆ T) :
    imageClosure S ⊆ imageClosure T :=
  fun _ hx q hq => hx q fun y hy => hq y (h hy)

/-- Taking the closure twice has the same equations as taking it once. -/
theorem imageClosure_idem {ι K : Type*} [Field K] (S : Set (ι → K)) :
    imageClosure (imageClosure S) = imageClosure S :=
  Set.Subset.antisymm (fun _ hx q hq => hx q fun _ hy => hy q hq) (subset_imageClosure _)

/-- Polynomial maps send a point of a closure into the closure of the image. -/
theorem imageClosure_polynomial {ι κ K : Type*} [Field K] {S : Set (ι → K)}
    {x : ι → K} (hx : x ∈ imageClosure S) (f : κ → MvPolynomial ι K) :
    (fun i => eval x (f i)) ∈ imageClosure ((fun y i => eval y (f i)) '' S) := by
  intro q hq
  have pullback (y : ι → K) : eval y (eval₂ C f q) = eval (fun i => eval y (f i)) q := by
    rw [eval_eval₂]
    have h : (eval y).comp C = RingHom.id K := by ext; simp
    rw [h, eval₂_id]
  rw [← pullback]
  exact hx _ fun y hy => (pullback y).trans (hq _ ⟨y, hy, rfl⟩)

/-- The set of degree-`d` vectors attained by circuits over `K` using at most `s` gates. -/
def circuitImage (K σ : Type*) [Field K] (d s : ℕ) : Set (DegreeMonomial σ d → K) :=
  {v | ∃ m ≤ s, ∃ c : VPVNP.Circuit K σ m, coeffVector d c.polynomial = v}

/-- Approximation in a given ambient field. For geometric border size the ambient field is
the algebraic closure of the original scalar field. -/
def geometricApprox {σ K : Type*} [Field K] (d s : ℕ) (p : MvPolynomial σ K) : Prop :=
  coeffVector d p ∈ imageClosure (circuitImage K σ d s)

/-- Section 2.1's approximation predicate over `F`. Both circuit labels and closure equations
are taken over `AlgebraicClosure F`. -/
def BorderApprox {σ F : Type*} [Field F] (d s : ℕ) (p : MvPolynomial σ F) : Prop :=
  geometricApprox d s (map (algebraMap F (AlgebraicClosure F)) p)

/-- More available gates preserve an approximation. -/
theorem geometricApprox_mono {σ K : Type*} [Field K] {d s t : ℕ} {p : MvPolynomial σ K}
    (h : geometricApprox d s p) (hst : s ≤ t) : geometricApprox d t p := by
  apply imageClosure_mono _ h
  rintro v ⟨m, hm, c, hc⟩
  exact ⟨m, hm.trans hst, c, hc⟩

/-- An exact formal output belongs to the geometric image at its circuit size. -/
theorem geometricApprox_circuitSize {σ K : Type*} [Field K] (d : ℕ) (p : MvPolynomial σ K) :
    geometricApprox d (VPVNP.circuitSize p) p := by
  obtain ⟨c, hc⟩ := VPVNP.circuitSize_spec p
  exact subset_imageClosure _ ⟨_, le_rfl, c, congrArg (coeffVector d) hc⟩

/-- An exact circuit over the original field gives a geometric approximation at the same size. -/
theorem borderApprox_circuitSize {σ F : Type*} [Field F] (d : ℕ) (p : MvPolynomial σ F) :
    BorderApprox d (VPVNP.circuitSize p) p :=
  geometricApprox_mono (geometricApprox_circuitSize d _)
    (VPVNP.circuitSize_map_le (algebraMap F (AlgebraicClosure F)) p)

/-- The least gate count in the projected image closure of §2.1. For homogeneous inputs of
degree `d` this is the manuscript's degree-component border size. -/
noncomputable def borderSize {σ F : Type*} [Field F] (d : ℕ) (p : MvPolynomial σ F) : ℕ := by
  classical
  exact Nat.find (show ∃ s, BorderApprox d s p from ⟨_, borderApprox_circuitSize d p⟩)

/-- A gate bound on the minimum is equivalent to the full image-closure condition. -/
theorem borderSize_le_iff {σ F : Type*} [Field F] {d s : ℕ} {p : MvPolynomial σ F} :
    borderSize d p ≤ s ↔ BorderApprox d s p := by
  classical
  rw [borderSize, Nat.find_le_iff]
  exact ⟨fun ⟨_, hm, h⟩ => geometricApprox_mono h hm, fun h => ⟨s, le_rfl, h⟩⟩

/-- The minimum is attained as a closure condition. -/
theorem borderSize_spec {σ F : Type*} [Field F] (d : ℕ) (p : MvPolynomial σ F) :
    BorderApprox d (borderSize d p) p := borderSize_le_iff.mp le_rfl

/-- Degree-component border size is bounded above by exact circuit size. -/
theorem borderSize_le_circuitSize {σ F : Type*} [Field F] (d : ℕ) (p : MvPolynomial σ F) :
    borderSize d p ≤ VPVNP.circuitSize p :=
  borderSize_le_iff.mpr (borderApprox_circuitSize d p)

end BorderVNP
end Computability
end OAI

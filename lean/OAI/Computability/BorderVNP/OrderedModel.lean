import OAI.Computability.BorderVNP.Model
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Ordered circuits and degree-component approximation

The free associative algebra has a basis indexed by words. Section 13 uses ordered binary
multiplication, with arbitrary reuse of previous gates. Approximation in degree `d` uses only
the coordinates of the words of length `d`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Ordered

/-- Noncommutative polynomials in the alphabet `σ`, with their word basis. -/
abbrev WordPoly (K σ : Type*) [CommRing K] := MonoidAlgebra K (FreeMonoid σ)

/-- The word with the given letters in the order of their positions. -/
def word {σ : Type*} {d : ℕ} (a : Fin d → σ) : FreeMonoid σ :=
  FreeMonoid.ofList (List.ofFn a)

/-- The degree-`d` word coefficients. -/
def coefficients {K σ : Type*} [CommRing K] (d : ℕ) (p : WordPoly K σ) :
    (Fin d → σ) → K := fun a => p.coeff (word a)

/-- Interpretation of a shared circuit in the word algebra. -/
noncomputable def output {K σ : Type*} [CommRing K] {s : ℕ} (c : VPVNP.Circuit K σ s) :
    WordPoly K σ :=
  c.eval (MonoidAlgebra.single 1) (fun a => MonoidAlgebra.single (FreeMonoid.of a) 1)

/-- The projected image of all ordered circuit shapes at a fixed binary gate bound. -/
def degreeImage (K σ : Type*) [Field K] (d s : ℕ) : Set ((Fin d → σ) → K) :=
  {v | ∃ m ≤ s, ∃ c : VPVNP.Circuit K σ m, coefficients d (output c) = v}

/-- Geometric border approximation over the algebraic closure of the coefficient field. -/
def approximates {F σ : Type*} [Field F] (d s : ℕ) (p : WordPoly F σ) : Prop :=
  (fun a => algebraMap F (AlgebraicClosure F) (coefficients d p a)) ∈
    imageClosure (degreeImage (AlgebraicClosure F) σ d s)

/-- Any word polynomial is computed by a finite shared ordered circuit. -/
theorem exists_output {K σ : Type*} [CommRing K] (p : WordPoly K σ) :
    ∃ n, ∃ c : VPVNP.Circuit K σ n, output c = p := by
  let P (f : WordPoly K σ) := ∃ n, ∃ c : VPVNP.Circuit K σ n, output c = f
  have combine (op : VPVNP.BinOp) {f g : WordPoly K σ} (hf : P f) (hg : P g) :
      P (op.apply f g) := by
    obtain ⟨_, c, rfl⟩ := hf
    obtain ⟨_, e, rfl⟩ := hg
    exact ⟨_, VPVNP.Circuit.combine op c e, VPVNP.Circuit.eval_combine ..⟩
  have constant (r : K) : P (MonoidAlgebra.single 1 r) :=
    ⟨0, VPVNP.Circuit.constant r, rfl⟩
  refine MonoidAlgebra.induction_on (motive := P) p ?_ (fun _ _ => combine .add) ?_
  · intro w
    induction w using FreeMonoid.recOn with
    | one => exact constant 1
    | of_mul a w ih =>
      rw [map_mul]
      exact combine .mul ⟨0, VPVNP.Circuit.variable a, rfl⟩ ih
  · intro r f hf
    rw [Algebra.smul_def]
    exact combine .mul (constant r) hf

/-- Every word polynomial has some finite border approximation in any specified degree. -/
theorem exists_approximation {F σ : Type*} [Field F] (d : ℕ) (p : WordPoly F σ) :
    ∃ s, approximates d s p := by
  obtain ⟨m, c, hc⟩ := exists_output
    (MonoidAlgebra.mapRingHom (FreeMonoid σ) (algebraMap F (AlgebraicClosure F)) p)
  refine ⟨m, subset_imageClosure _ ⟨m, le_rfl, c, ?_⟩⟩
  rw [hc]
  funext a
  exact MonoidAlgebra.coeff_mapRingHom ..

/-- Least gate count for approximating the specified length of words. -/
noncomputable def borderSize {F σ : Type*} [Field F] (d : ℕ) (p : WordPoly F σ) : ℕ := by
  classical
  exact Nat.find (exists_approximation d p)

/-- The minimum is equivalent to the projected image-closure definition. -/
theorem borderSize_le_iff {F σ : Type*} [Field F] {d s : ℕ} {p : WordPoly F σ} :
    borderSize d p ≤ s ↔ approximates d s p := by
  classical
  rw [borderSize, Nat.find_le_iff]
  refine ⟨?_, fun h => ⟨_, le_rfl, h⟩⟩
  rintro ⟨t, ht, h⟩
  apply imageClosure_mono _ h
  rintro v ⟨m, hm, c, hc⟩
  exact ⟨m, hm.trans ht, c, hc⟩

/-- The permutation word in increasing row order, with its sign in the determinant case. -/
noncomputable def rowPolynomial (F : Type*) [CommRing F] (n : ℕ) (signed : Bool) :
    WordPoly F (Fin n × Fin n) :=
  ∑ π : Equiv.Perm (Fin n), MonoidAlgebra.single (word fun i => (i, π i))
    (if signed then (((Equiv.Perm.sign π : ℤˣ) : ℤ) : F) else 1)

/-- Substitution of arbitrary, possibly noncommuting, elements for the letters. -/
noncomputable def substitute {K σ A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (v : σ → A) : WordPoly K σ →ₐ[K] A :=
  MonoidAlgebra.lift K A (FreeMonoid σ) (FreeMonoid.lift v)

/-- After substitution the matrix entries in each term are still multiplied in row order. -/
theorem substitute_rowPolynomial {F A : Type*} [CommRing F] [Ring A] [Algebra F A]
    (n : ℕ) (signed : Bool) (v : Fin n × Fin n → A) :
    substitute v (rowPolynomial F n signed) =
      ∑ π : Equiv.Perm (Fin n), (if signed then (((Equiv.Perm.sign π : ℤˣ) : ℤ) : F) else 1)
        • (List.ofFn fun i => v (i, π i)).prod := by
  simp only [rowPolynomial, map_sum, substitute, MonoidAlgebra.lift_single, word,
    FreeMonoid.lift_ofList, List.map_ofFn, Function.comp_def]

end Ordered

end BorderVNP
end Computability
end OAI

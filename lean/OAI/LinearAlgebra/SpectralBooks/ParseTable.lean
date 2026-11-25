import OAI.LinearAlgebra.SpectralBooks.BorderCircuit
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Integral graded parse tables for homogeneous circuit outputs

Each node of an ordered parse chooses a variable at a leaf or an ordered pair of slots at
a product. Natural index `k` in `parseForm` denotes homogeneous degree `k + 1`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MvPolynomial
open scoped Classical

noncomputable section

/-- A leaf weight or a product weight indexed by the parent slot, degree, split, and child slots. -/
abbrev ParseParameter (n : ℕ) (G σ : Type*) := (G × σ) ⊕ (G × Fin (n+1) × Fin (n+1) × G × G)

variable {n : ℕ} {G σ R S : Type*} [Fintype G] [Fintype σ] [CommSemiring R] [CommSemiring S]

/-- The form of degree `k+1` in the designated slot. At degrees up to `n` all degree and split
indices lie in the parameter format without wrapping. -/
def parseForm (x : ParseParameter n G σ → R) : ℕ → G → MvPolynomial σ R
  | 0, g => ∑ i, C (x (.inl (g,i))) * X i
  | k + 1, g => ∑ q : Fin (k+1) × G × G,
      C (x (.inr (g, Fin.ofNat (n+1) k, Fin.ofNat (n+1) q.1.val, q.2.1, q.2.2))) *
        parseForm x q.1.val q.2.1 * parseForm x (k-q.1.val) q.2.2
termination_by k _ => k
decreasing_by all_goals have := q.1.isLt; omega

theorem parseForm_zero (x : ParseParameter n G σ → R) (g : G) :
    parseForm x 0 g = ∑ i, C (x (.inl (g,i))) * X i := by rw [parseForm]

theorem parseForm_succ (x : ParseParameter n G σ → R) (k : ℕ) (g : G) :
    parseForm x (k+1) g = ∑ q : Fin (k+1) × G × G,
      C (x (.inr (g, Fin.ofNat (n+1) k, Fin.ofNat (n+1) q.1.val, q.2.1, q.2.2))) *
        parseForm x q.1.val q.2.1 * parseForm x (k-q.1.val) q.2.2 := by rw [parseForm]

/-- The universal parse polynomial specializes over every coefficient semiring. -/
theorem map_parseForm (f : R →+* S) (x : ParseParameter n G σ → R) (k : ℕ) (g : G) :
    map f (parseForm x k g) = parseForm (f ∘ x) k g := by
  induction k using Nat.strong_induction_on generalizing g with
  | h k ih =>
    cases k with
    | zero => simp only [parseForm_zero, map_sum, map_mul, map_C, map_X, Function.comp_apply]
    | succ k =>
      rw [parseForm_succ, parseForm_succ, map_sum]
      apply Finset.sum_congr rfl
      intro q _
      simp only [map_mul, map_C, Function.comp_apply, ih _ q.1.isLt,
        ih _ (Nat.lt_succ_of_le (Nat.sub_le _ _))]

/-- The integral coordinate map in the full space of homogeneous degree-`n` coefficients. -/
def parseCoordinates (n : ℕ) (g : G) (m : DegreeMonomial σ n) :
    MvPolynomial (ParseParameter n G σ) ℤ :=
  (parseForm (X : ParseParameter n G σ → MvPolynomial _ ℤ) (n - 1) g).coeff m.val

theorem eval₂_parseCoordinates {R : Type*} [CommRing R] (g : G) (m : DegreeMonomial σ n)
    (x : ParseParameter n G σ → R) :
    eval₂ (Int.castRingHom R) x (parseCoordinates n g m) = (parseForm x (n - 1) g).coeff m.val := by
  let f := eval₂Hom (Int.castRingHom R) x
  have hx : f ∘ (X : ParseParameter n G σ → MvPolynomial _ ℤ) = x := by
    funext j
    exact eval₂_X _ _ j
  have h := map_parseForm f (X : ParseParameter n G σ → MvPolynomial _ ℤ) (n - 1) g
  rw [hx] at h
  exact (coeff_map f _ _).symm.trans (congrArg (fun p : MvPolynomial σ R ↦ p.coeff m.val) h)

end

end SpectralBooks
end LinearAlgebra
end OAI

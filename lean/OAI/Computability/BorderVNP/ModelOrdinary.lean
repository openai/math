import OAI.Computability.BorderVNP.Model
import OAI.Computability.VPVNP.Classes
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Full coefficient closure and the ordinary border class

The degree of a formal output is at most two to the number of binary gates. Thus at each
size the ordinary closure can be taken in the finite space of all coefficients through
that degree, with higher coefficients zero. Projecting this closure to any one degree
gives the weaker approximation condition of §2.1.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial VPVNP

variable {σ K : Type*} [Field K]

private theorem read_degree_bound {m : ℕ} (r : Ref K σ m)
    (w : Fin m → MvPolynomial σ K) (hw : ∀ i, (w i).totalDegree ≤ 2 ^ m) :
    (r.read C X w).totalDegree ≤ 2 ^ m := by
  cases r with
  | var i => simpa only [Ref.read, totalDegree_X] using Nat.one_le_pow m 2 (by decide)
  | const a => simp [Ref.read]
  | gate j => exact hw j

private theorem gate_degree_bound {m : ℕ} (P : Program K σ m) (i : Fin m) :
    (P.run C X i).totalDegree ≤ 2 ^ m := by
  induction P with
  | nil => exact Fin.elim0 i
  | @snoc n P op l r ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Program.run, Fin.lastCases_last, pow_succ]
      have hl := read_degree_bound l (P.run C X) ih
      have hr := read_degree_bound r (P.run C X) ih
      cases op with
      | add => exact (totalDegree_add ..).trans ((max_le hl hr).trans (by omega))
      | sub => exact (totalDegree_sub ..).trans ((max_le hl hr).trans (by omega))
      | mul => exact (totalDegree_mul ..).trans (by omega)
    · simp only [Program.run, Fin.lastCases_castSucc, pow_succ]
      exact (ih j).trans (by omega)

/-- The total degree of a circuit output is bounded in terms of its number of arithmetic
gates alone, including size-zero outputs. -/
theorem circuit_degree_bound {m : ℕ} (c : Circuit K σ m) : c.polynomial.totalDegree ≤ 2 ^ m :=
  read_degree_bound c.output _ (gate_degree_bound c.program)

/-- All coefficient vectors, with every degree retained, at a given gate bound. -/
def fullCircuitImage (K σ : Type*) [Field K] (s : ℕ) : Set ((σ →₀ ℕ) → K) :=
  {v | ∃ m ≤ s, ∃ c : Circuit K σ m, c.polynomial.coeff = v}

/-- Every high-degree coordinate vanishes on the full size-bounded image. -/
theorem fullCircuitImage_zero_above {s : ℕ} {v : (σ →₀ ℕ) → K} (hv : v ∈ fullCircuitImage K σ s)
    {i : σ →₀ ℕ} (hi : 2 ^ s < i.degree) : v i = 0 := by
  obtain ⟨m, hm, c, rfl⟩ := hv
  by_contra h
  exact hi.not_ge ((le_totalDegree (mem_support_iff.mpr h)).trans
    ((circuit_degree_bound c).trans (Nat.pow_le_pow_right (by decide) hm)))

/-- The ordinary geometric border predicate over the given ambient field. -/
def geometricFullApprox (s : ℕ) (p : MvPolynomial σ K) : Prop :=
  (fun i => p.coeff i) ∈ imageClosure (fullCircuitImage K σ s)

/-- The coordinate subspace containing all full outputs at a fixed size is finite
dimensional when the variable type is finite. -/
abbrev BoundedMonomial (σ : Type*) (D : ℕ) := {m : σ →₀ ℕ // m.degree ≤ D}

instance {σ : Type*} [Finite σ] (D : ℕ) : Finite (BoundedMonomial σ D) :=
  Finsupp.finite_of_degree_le D

/-- Full border approximation is equivalent to taking a finite coefficient closure through
degree `2 ^ s` and imposing vanishing of every higher coefficient of the target. -/
theorem geometricFullApprox_iff_cutoff (s : ℕ) (p : MvPolynomial σ K) :
    geometricFullApprox s p ↔
      (∀ i : σ →₀ ℕ, 2 ^ s < i.degree → p.coeff i = 0) ∧
      (fun i : BoundedMonomial σ (2 ^ s) => p.coeff i.val) ∈
        imageClosure ((fun (v : (σ →₀ ℕ) → K) (i : BoundedMonomial σ (2 ^ s)) => v i.val) ''
          fullCircuitImage K σ s) := by
  classical
  constructor
  · intro h
    constructor
    · intro i hi
      simpa only [eval_X] using h (X i) fun v hv => by
        simpa only [eval_X] using fullCircuitImage_zero_above hv hi
    · simpa only [eval_X] using imageClosure_polynomial h
        (fun i : BoundedMonomial σ (2 ^ s) => X i.val)
  · rintro ⟨hvan, hbounded⟩
    let extend (i : σ →₀ ℕ) : MvPolynomial (BoundedMonomial σ (2 ^ s)) K :=
      if hi : i.degree ≤ 2 ^ s then X ⟨i, hi⟩ else 0
    have recover (v : (σ →₀ ℕ) → K) (hv : ∀ i, 2 ^ s < i.degree → v i = 0) :
        (fun i => eval (fun j : BoundedMonomial σ (2 ^ s) => v j.val) (extend i)) = v := by
      funext i
      by_cases hi : i.degree ≤ 2 ^ s
      · simp only [extend, dite_eq_left hi, eval_X]
      · simp [extend, hi, hv i (Nat.lt_of_not_ge hi)]
    rw [geometricFullApprox, ← recover p.coeff hvan]
    refine imageClosure_mono ?_ (imageClosure_polynomial hbounded extend)
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    change (fun i => eval (fun j : BoundedMonomial σ (2 ^ s) => v j.val) (extend i)) ∈ _
    rw [recover v fun _ hi => fullCircuitImage_zero_above hv hi]
    exact hv

/-- Ordinary border approximation takes the closure of the entire output over the
algebraic closure of the scalar field. -/
def OrdinaryApprox (s : ℕ) (p : MvPolynomial σ K) : Prop :=
  geometricFullApprox s (map (algebraMap K (AlgebraicClosure K)) p)

/-- Projecting the entire output to degree `d` is a coordinate selection. -/
theorem geometricApprox_of_full {s : ℕ} {p : MvPolynomial σ K} (h : geometricFullApprox s p)
    (d : ℕ) : geometricApprox d s p := by
  have hc := imageClosure_polynomial h (fun i : DegreeMonomial σ d => (X i.val))
  simp only [eval_X] at hc
  apply imageClosure_mono _ hc
  rintro _ ⟨_, ⟨m, hm, c, rfl⟩, rfl⟩
  exact ⟨m, hm, c, rfl⟩

/-- Full approximation over the algebraic closure implies the component approximation
with the same gate bound. -/
theorem borderApprox_of_ordinary {s : ℕ} {p : MvPolynomial σ K} (h : OrdinaryApprox s p)
    (d : ℕ) : BorderApprox d s p := geometricApprox_of_full h d

/-- The usual nonuniform border VP class, with polynomially bounded variable count, degree,
and full-output geometric circuit size. -/
def IsBorderVP {X : ℕ → Type} [∀ n, Fintype (X n)] (p : Family K X) : Prop :=
  PFamily p ∧ ∃ s : ℕ → ℕ, PolynomiallyBounded s ∧ ∀ n, OrdinaryApprox (s n) (p n)

/-- A superpolynomial degree-component border lower bound excludes the usual border VP
class, even when a different degree is selected at each family index. -/
theorem not_isBorderVP_of_eventual_size {X : ℕ → Type} [∀ n, Fintype (X n)] {p : Family K X}
    {d : ℕ → ℕ} (h : EventuallySuperpolynomial (fun n => borderSize (d n) (p n))) :
    ¬ IsBorderVP p := by
  rintro ⟨_, s, ⟨A, b, N, hs⟩, hp⟩
  apply h.not_polynomially_bounded
  exact ⟨A, b, N, fun n hn =>
    (borderSize_le_iff.mpr (borderApprox_of_ordinary (hp n) _)).trans (hs n hn)⟩

end BorderVNP
end Computability
end OAI

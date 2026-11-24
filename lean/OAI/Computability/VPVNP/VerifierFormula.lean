import OAI.Computability.VPVNP.CircuitComposition
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fintype.BigOperators

/-!
# Arithmetic formulas for Boolean witness verification

Formulas give explicit circuits for products of local constraints in a VNP summand.
Compilation uses one gate per binary node, including products of constants.
-/

namespace OAI
namespace Computability
namespace VPVNP

variable {R σ A ι : Type*}

/-- An arithmetic formula with scalar and variable leaves. -/
inductive Formula (R σ : Type*) where
  | const : R → Formula R σ
  | var : σ → Formula R σ
  | bin : BinOp → Formula R σ → Formula R σ → Formula R σ

namespace Formula

/-- Form a binary addition node with summands `a` and `b`. -/
abbrev add (a b : Formula R σ) := bin .add a b
/-- Form a binary subtraction node with minuend `a` and subtrahend `b`. -/
abbrev sub (a b : Formula R σ) := bin .sub a b
/-- Form a binary multiplication node with factors `a` and `b` in that order. -/
abbrev mul (a b : Formula R σ) := bin .mul a b

/-- Gate count excludes scalar and variable leaves. -/
def size : Formula R σ → ℕ
  | .const _ | .var _ => 0
  | .bin _ a b => a.size + b.size + 1

/-- Syntactic degree bounds the degree of the formal polynomial even after cancellation. -/
def degree : Formula R σ → ℕ
  | .const _ => 0
  | .var _ => 1
  | .bin .add a b | .bin .sub a b => max a.degree b.degree
  | .bin .mul a b => a.degree + b.degree

/-- Evaluate a formula in the ring `A`, interpreting each constant with `s`, each variable with
`x`, and each binary node by its ring operation. -/
def eval [Ring A] (s : R → A) (x : σ → A) : Formula R σ → A
  | .const r => s r
  | .var i => x i
  | .bin op a b => op.apply (a.eval s x) (b.eval s x)

/-- The formal multivariate polynomial represented by a formula over a commutative ring,
interpreting constants by `MvPolynomial.C` and variables by `MvPolynomial.X`. -/
noncomputable def polynomial [CommRing R] (f : Formula R σ) : MvPolynomial σ R :=
  f.eval MvPolynomial.C MvPolynomial.X

/-- Compile the formula to a straight-line program of exactly its binary node count. -/
def compile : (f : Formula R σ) → Circuit R σ f.size
  | .const r => ⟨.nil, .const r⟩
  | .var i => ⟨.nil, .var i⟩
  | .bin op a b => Circuit.combine op a.compile b.compile

theorem compile_eval [Ring A] (f : Formula R σ) (s : R → A) (x : σ → A) :
    f.compile.eval s x = f.eval s x := by
  induction f with
  | const | var => rfl
  | bin op a b ha hb =>
    exact (Circuit.eval_combine op a.compile b.compile s x).trans (congrArg₂ op.apply ha hb)

@[simp] theorem compile_polynomial [CommRing R] (f : Formula R σ) :
    f.compile.polynomial = f.polynomial := compile_eval _ _ _

theorem totalDegree_le [CommRing R] (f : Formula R σ) : f.polynomial.totalDegree ≤ f.degree := by
  induction f with
  | const r => simp [polynomial, eval, degree]
  | var i =>
    rcases subsingleton_or_nontrivial R with h | h
    · have he : (var i : Formula R σ).polynomial = 0 := Subsingleton.elim _ _
      simp [he]
    · simp [polynomial, eval, degree]
  | bin op a b ha hb =>
    cases op with
    | add => exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max ha hb)
    | sub => exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ha hb)
    | mul => exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha hb)

/-- Product of a finite family of formulas, starting with a scalar one. -/
noncomputable def prod [Fintype ι] [One R] (f : ι → Formula R σ) : Formula R σ :=
  Finset.univ.toList.foldr (fun i acc => mul (f i) acc) (.const 1)

@[simp] theorem size_prod [Fintype ι] [One R] (f : ι → Formula R σ) :
    (prod f).size = (∑ i, (f i).size) + Fintype.card ι := by
  have aux (l : List ι) :
      (l.foldr (fun i acc => mul (f i) acc) (.const 1)).size =
        (l.map (fun i => (f i).size)).sum + l.length := by
    induction l with
    | nil => rfl
    | cons i l ih => simp [size, ih, Nat.add_assoc]
  simp [prod, aux, Finset.sum_map_toList, Finset.length_toList]

@[simp] theorem degree_prod [Fintype ι] [One R] (f : ι → Formula R σ) :
    (prod f).degree = ∑ i, (f i).degree := by
  have aux (l : List ι) :
      (l.foldr (fun i acc => mul (f i) acc) (.const 1)).degree =
        (l.map (fun i => (f i).degree)).sum := by
    induction l with
    | nil => rfl
    | cons i l ih => simp [degree, ih]
  simp [prod, aux, Finset.sum_map_toList]

theorem eval_prod [Fintype ι] [One R] [CommRing A] (f : ι → Formula R σ)
    (s : R → A) (x : σ → A) (hs : s 1 = 1) :
    (prod f).eval s x = ∏ i, (f i).eval s x := by
  have aux (l : List ι) :
      (l.foldr (fun i acc => mul (f i) acc) (.const 1)).eval s x =
        (l.map (fun i => (f i).eval s x)).prod := by
    induction l with
    | nil => exact hs
    | cons i l ih => simp [eval, BinOp.apply, ih]
  simp [prod, aux, Finset.prod_map_toList]

@[simp] theorem polynomial_prod [Fintype ι] [CommRing R] (f : ι → Formula R σ) :
    (prod f).polynomial = ∏ i, (f i).polynomial :=
  eval_prod f MvPolynomial.C MvPolynomial.X (map_one _)

end Formula

end VPVNP
end Computability
end OAI

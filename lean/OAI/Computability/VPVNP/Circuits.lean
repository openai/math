import Mathlib.Algebra.MvPolynomial.Eval

/-! # Exact arithmetic circuits and projections

Gates are listed in topological order. Each operand may use any earlier gate, a variable,
or any scalar in the coefficient ring. Only binary operations count toward the size.
The designated output is evaluated in the ring of formal multivariate polynomials.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- A binary addition, subtraction, or multiplication gate in an exact arithmetic circuit. -/
inductive BinOp where
  | add | sub | mul

/-- Interpret a gate's operation on its two ordered inputs in the target ring. -/
def BinOp.apply {A : Type*} [Ring A] : BinOp → A → A → A
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- A reference available after exactly `n` gates have been computed. -/
inductive Ref (R σ : Type*) (n : ℕ) where
  | var : σ → Ref R σ n
  | const : R → Ref R σ n
  | gate : Fin n → Ref R σ n

/-- A topologically ordered list of arithmetic gates. The index counts the gates already
available to subsequent operands. -/
inductive Program (R σ : Type*) : ℕ → Type _ where
  | nil : Program R σ 0
  | snoc {n : ℕ} (prev : Program R σ n) (op : BinOp) (a b : Ref R σ n) : Program R σ (n+1)

/-- An arithmetic program with one designated output. Its size index counts binary operations. -/
structure Circuit (R σ : Type*) (n : ℕ) where
  /-- The sequence of binary gates available to the output reference. -/
  program : Program R σ n
  /-- The input variable, ring constant, or previously computed gate selected as the output. -/
  output : Ref R σ n

variable {R S σ τ A B : Type*} {n : ℕ}

/-- Resolve an operand using the supplied interpretation of constants, inputs, and earlier gate
values. -/
def Ref.read (scalar : R → A) (input : σ → A) (wires : Fin n → A) : Ref R σ n → A
  | .const r => scalar r
  | .var i => input i
  | .gate i => wires i

/-- Evaluate the gates in topological order and return the value at every gate index. -/
def Program.run [Ring A] (scalar : R → A) (input : σ → A) :
    {n : ℕ} → Program R σ n → Fin n → A
  | _, .nil => Fin.elim0
  | _, .snoc p op a b =>
    let wires := p.run scalar input
    Fin.lastCases (op.apply (a.read scalar input wires) (b.read scalar input wires)) wires

/-- Read the designated output after evaluating the circuit with the supplied scalar and
variable assignments. -/
def Circuit.eval [Ring A] (c : Circuit R σ n) (scalar : R → A) (input : σ → A) : A :=
  c.output.read scalar input (c.program.run scalar input)

/-- The formal polynomial computed when each input is its corresponding indeterminate and each
scalar is a constant polynomial. -/
noncomputable def Circuit.polynomial [CommRing R] (c : Circuit R σ n) : MvPolynomial σ R :=
  c.eval MvPolynomial.C MvPolynomial.X

/-- Substitutions allowed in a projection. A variable may become a variable or a scalar. -/
abbrev Projection (R σ τ : Type*) := σ → τ ⊕ R

/-- Apply a projection to a variable operand and the supplied scalar map to a constant operand.
A gate reference keeps its index. -/
def Ref.subst (φ : Projection S σ τ) (f : R → S) : Ref R σ n → Ref S τ n
  | .var i => (φ i).elim Ref.var Ref.const
  | .const r => .const (f r)
  | .gate i => .gate i

/-- Project the variable operands and map the constants of every gate in the program. -/
def Program.subst (φ : Projection S σ τ) (f : R → S) :
    {n : ℕ} → Program R σ n → Program S τ n
  | _, .nil => .nil
  | _, .snoc p op a b => .snoc (p.subst φ f) op (a.subst φ f) (b.subst φ f)

/-- Apply the same variable projection and scalar map to the program and its designated output
reference. -/
def Circuit.subst (c : Circuit R σ n) (φ : Projection S σ τ) (f : R → S) : Circuit S τ n :=
  ⟨c.program.subst φ f, c.output.subst φ f⟩

/-- Specialize each scalar operand along the given map while retaining the circuit's input
variables. -/
def Circuit.mapConstants (c : Circuit R σ n) (f : R → S) : Circuit S σ n :=
  c.subst Sum.inl f

private theorem Ref.read_subst (φ : Projection S σ τ) (f : R → S)
    (s : S → A) (x : τ → A) (w : Fin n → A) (r : Ref R σ n) :
    (r.subst φ f).read s x w = r.read (s ∘ f) (fun i => (φ i).elim x s) w := by
  cases r with
  | var i => cases h : φ i <;> simp [Ref.subst, Ref.read, h]
  | const | gate => rfl

private theorem Program.run_subst [Ring A] (φ : Projection S σ τ) (f : R → S)
    (s : S → A) (x : τ → A) (p : Program R σ n) :
    (p.subst φ f).run s x = p.run (s ∘ f) (fun i => (φ i).elim x s) := by
  induction p with
  | nil => rfl
  | snoc p op a b ih => simp only [Program.subst, Program.run, ih, Ref.read_subst]

theorem Circuit.eval_subst [Ring A] (c : Circuit R σ n) (φ : Projection S σ τ)
    (f : R → S) (s : S → A) (x : τ → A) :
    (c.subst φ f).eval s x = c.eval (s ∘ f) (fun i => (φ i).elim x s) := by
  simp only [Circuit.eval, Circuit.subst, Program.run_subst, Ref.read_subst]

private theorem Ref.read_hom [Ring A] [Ring B] (h : A →+* B) (s : R → A) (x : σ → A)
    (w : Fin n → A) (r : Ref R σ n) :
    h (r.read s x w) = r.read (h ∘ s) (h ∘ x) (h ∘ w) := by cases r <;> rfl

private theorem Program.run_hom [Ring A] [Ring B] (h : A →+* B) (s : R → A) (x : σ → A)
    (p : Program R σ n) : h ∘ p.run s x = p.run (h ∘ s) (h ∘ x) := by
  induction p with
  | nil => funext j; exact j.elim0
  | snoc p op a b ih =>
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Function.comp_apply, Program.run, Fin.lastCases_last]
      cases op <;> simp [BinOp.apply, Ref.read_hom, ih]
    · simpa [Program.run, Function.comp_def] using congrFun ih i

theorem Circuit.eval_hom [Ring A] [Ring B] (c : Circuit R σ n) (h : A →+* B)
    (s : R → A) (x : σ → A) : h (c.eval s x) = c.eval (h ∘ s) (h ∘ x) := by
  simp only [Circuit.eval, Ref.read_hom, Program.run_hom]

/-- Scalar specialization preserves every binary gate of the circuit. -/
theorem Circuit.map_polynomial [CommRing R] [CommRing S] (c : Circuit R σ n) (f : R →+* S) :
    (c.mapConstants f).polynomial = MvPolynomial.map f c.polynomial := by
  rw [Circuit.mapConstants, Circuit.polynomial, Circuit.eval_subst, Circuit.polynomial,
    Circuit.eval_hom]
  congr 1 <;> funext i <;> simp

/-- The coefficient-preserving polynomial semiring homomorphism substituting each source
variable by its prescribed target variable or scalar. -/
noncomputable def Projection.hom [CommSemiring R] (φ : Projection R σ τ) :
    MvPolynomial σ R →+* MvPolynomial τ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => (φ i).elim MvPolynomial.X MvPolynomial.C)

/-- Projecting a formal polynomial computed with `n` gates gives an `n`-gate circuit. -/
theorem Circuit.project_polynomial [CommRing R] (c : Circuit R σ n) (φ : Projection R σ τ) :
    (c.subst φ id).polynomial = φ.hom c.polynomial := by
  rw [Circuit.polynomial, Circuit.eval_subst, Circuit.polynomial, Circuit.eval_hom]
  congr 1 <;> funext i <;> simp [Projection.hom]

end VPVNP
end Computability
end OAI

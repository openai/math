import OAI.Computability.VPVNP.BooleanTranscript
import OAI.Computability.VPVNP.VerifierFormula

/-!
# Arithmetic formulas for a Boolean verifier's transcript

A reference reads either a Boolean constant, an input variable or a proposed gate
value. With all transcript values provided as variables, checking one AND or NOT
gate takes eight binary arithmetic operations and has syntactic degree at most
three. The final acceptance test multiplies this product by the output bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BooleanTranscript

variable {σ τ R A : Type*} [CommRing R] {n : ℕ}

private def refFormula (r : Ref Bool σ n) (input : σ → τ) (wires : Fin n → τ) : Formula R τ :=
  r.read (fun b => .const (bit b)) (fun i => .var (input i)) (fun i => .var (wires i))

private theorem eval_refFormula [CommRing A] (r : Ref Bool σ n) (input : σ → τ)
    (wires : Fin n → τ) (s : R →+* A) (x : τ → A) :
    (refFormula r input wires).eval s x = r.read bit (x ∘ input) (x ∘ wires) := by
  cases r with
  | const b => cases b <;> simp [refFormula, Ref.read, bit, Formula.eval]
  | var | gate => rfl

private theorem size_refFormula (r : Ref Bool σ n) (input : σ → τ) (wires : Fin n → τ) :
    (refFormula (R := R) r input wires).size = 0 := by
  cases r <;> rfl

private theorem degree_refFormula (r : Ref Bool σ n) (input : σ → τ) (wires : Fin n → τ) :
    (refFormula (R := R) r input wires).degree ≤ 1 := by
  cases r <;> simp [refFormula, Ref.read, Formula.degree]

private def Gate.arithFormula (g : Gate σ n) (input : σ → τ) (wires : Fin n → τ) : Formula R τ :=
  match g with
  | .and a b => (refFormula a input wires).mul (refFormula b input wires)
  | .not a => (.const (1 : R) : Formula R τ).sub (refFormula a input wires)

private theorem Gate.eval_arithFormula [CommRing A] (g : Gate σ n) (input : σ → τ)
    (wires : Fin n → τ) (s : R →+* A) (x : τ → A) :
    (g.arithFormula input wires).eval s x = g.arith (x ∘ input) (x ∘ wires) := by
  cases g <;> simp [arithFormula, arith, Formula.mul, Formula.sub, Formula.eval,
    BinOp.apply, eval_refFormula]

private theorem Gate.size_arithFormula (g : Gate σ n) (input : σ → τ) (wires : Fin n → τ) :
    (g.arithFormula (R := R) input wires).size = 1 := by
  cases g <;> simp [arithFormula, Formula.mul, Formula.sub, Formula.size, size_refFormula]

private theorem Gate.degree_arithFormula (g : Gate σ n) (input : σ → τ) (wires : Fin n → τ) :
    (g.arithFormula (R := R) input wires).degree ≤ 2 := by
  cases g with
  | and a b => exact Nat.add_le_add (degree_refFormula a input wires) (degree_refFormula b input wires)
  | not a => exact max_le (Nat.zero_le _) ((degree_refFormula a input wires).trans (by decide))

private def testFormula (a b : Formula R τ) : Formula R τ :=
  (a.mul b).add (((Formula.const 1).sub a).mul ((Formula.const 1).sub b))

private theorem eval_testFormula [CommRing A] (a b : Formula R τ) (s : R →+* A) (x : τ → A) :
    (testFormula a b).eval s x = equalBit (a.eval s x) (b.eval s x) := by
  simp [testFormula, Formula.add, Formula.sub, Formula.mul, Formula.eval, BinOp.apply, equalBit]

private theorem size_testFormula (a b : Formula R τ) :
    (testFormula a b).size = 2 * a.size + 2 * b.size + 5 := by
  simp only [testFormula, Formula.add, Formula.sub, Formula.mul, Formula.size]
  omega

private theorem degree_testFormula (a b : Formula R τ) :
    (testFormula a b).degree = a.degree + b.degree := by
  simp [testFormula, Formula.add, Formula.sub, Formula.mul, Formula.degree]

/-- Product of local consistency tests for the proposed gate values. -/
def Program.checkFormula (input : σ → τ) : {n : ℕ} → Program σ n → (Fin n → τ) → Formula R τ
  | _, .nil, _ => .const 1
  | k + 1, .snoc p g, wires => (p.checkFormula input (Fin.init wires)).mul
      (testFormula (g.arithFormula input (Fin.init wires)) (.var (wires (Fin.last k))))

private theorem Program.eval_checkFormula [CommRing A] (p : Program σ n) (input : σ → τ)
    (wires : Fin n → τ) (s : R →+* A) (x : τ → A) :
    (p.checkFormula input wires).eval s x = p.check (x ∘ input) (x ∘ wires) := by
  induction p with
  | nil => simp [checkFormula, check, Formula.eval]
  | snoc p g ih =>
    simp [checkFormula, check, Formula.mul, Formula.eval, BinOp.apply, eval_testFormula,
      Gate.eval_arithFormula, ih, Fin.comp_init]

private theorem Program.size_checkFormula (p : Program σ n) (input : σ → τ) (wires : Fin n → τ) :
    (p.checkFormula (R := R) input wires).size = 8 * n := by
  induction p with
  | nil => rfl
  | snoc p g ih =>
    simp only [checkFormula, Formula.mul, Formula.size, size_testFormula, Gate.size_arithFormula, ih]
    omega

private theorem Program.degree_checkFormula_le (p : Program σ n) (input : σ → τ)
    (wires : Fin n → τ) : (p.checkFormula (R := R) input wires).degree ≤ 3 * n := by
  induction p with
  | nil => rfl
  | @snoc k p g ih =>
    simp only [checkFormula, Formula.mul, Formula.degree, degree_testFormula]
    have := g.degree_arithFormula (R := R) input (Fin.init wires)
    have := ih (Fin.init wires)
    omega

/-- Formula for the product of all gate tests and the designated output. -/
def Circuit.weightFormula (c : Circuit σ n) (input : σ → τ) (wires : Fin n → τ) : Formula R τ :=
  (c.program.checkFormula input wires).mul (refFormula c.output input wires)

theorem Circuit.eval_weightFormula [CommRing A] (c : Circuit σ n) (input : σ → τ)
    (wires : Fin n → τ) (s : R →+* A) (x : τ → A) :
    (c.weightFormula input wires).eval s x = c.weight (x ∘ input) (x ∘ wires) := by
  simp [weightFormula, weight, Formula.mul, Formula.eval, BinOp.apply,
    Program.eval_checkFormula, eval_refFormula]

theorem Circuit.size_weightFormula_le (c : Circuit σ n) (input : σ → τ) (wires : Fin n → τ) :
    (c.weightFormula (R := R) input wires).size ≤ 8 * n + 1 := by
  simp [weightFormula, Formula.mul, Formula.size, Program.size_checkFormula, size_refFormula]

theorem Circuit.degree_weightFormula_le (c : Circuit σ n) (input : σ → τ) (wires : Fin n → τ) :
    (c.weightFormula (R := R) input wires).degree ≤ 3 * n + 1 :=
  Nat.add_le_add (c.program.degree_checkFormula_le input wires) (degree_refFormula c.output input wires)

end BooleanTranscript

end VPVNP
end Computability
end OAI

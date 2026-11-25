import OAI.Computability.BorderVNP.ModelInterpretedGate

/-! # Extending a circuit while retaining its available operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Homogenize

open VPVNP MvPolynomial

variable {R σ : Type*} [CommRing R] {n m : ℕ}

/-- A formal polynomial is already available as an input, scalar, or gate output. -/
def HasWire (p : Program R σ n) (f : MvPolynomial σ R) : Prop :=
  ∃ r : Ref R σ n, r.read C X (p.run C X) = f

/-- Every operand of the first program can be reused in the second. -/
def Preserves (p : Program R σ n) (q : Program R σ m) : Prop :=
  ∀ f, HasWire p f → HasWire q f

/-- Scalars are free circuit inputs. -/
theorem hasWire_const (p : Program R σ n) (a : R) : HasWire p (C a) :=
  ⟨.const a, rfl⟩

/-- Variables are free circuit inputs. -/
theorem hasWire_var (p : Program R σ n) (x : σ) : HasWire p (X x) :=
  ⟨.var x, rfl⟩

/-- Appending a binary operation retains all old operands and produces its result. -/
theorem append_binary (p : Program R σ n) (op : BinOp) {a b : MvPolynomial σ R}
    (ha : HasWire p a) (hb : HasWire p b) :
    ∃ q : Program R σ (n+1), Preserves p q ∧ HasWire q (op.apply a b) :=
  Interpreted.append_binary C X p op ha hb

/-- Produce a finite sequence of operands at bounded cost per operand. Every operand is
available for all subsequent steps. -/
theorem extend_fin (p : Program R σ n) (k t : ℕ) (f : ℕ → MvPolynomial σ R)
    (step : ∀ {m} (q : Program R σ m), Preserves p q → ∀ i < k,
      ∃ l ≤ m+t, ∃ r : Program R σ l, Preserves q r ∧ HasWire r (f i)) :
    ∃ l ≤ n+k*t, ∃ r : Program R σ l, Preserves p r ∧ ∀ i < k, HasWire r (f i) :=
  Interpreted.extend_fin C X p k t f step

end Homogenize

end BorderVNP
end Computability
end OAI

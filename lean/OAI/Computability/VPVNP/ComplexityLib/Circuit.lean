import OAI.Computability.VPVNP.ComplexityLib.ToUpstream
import Complexity.Computability.Circuit.Arithmetic.VP
import OAI.Computability.VPVNP.CircuitSize

/-! # Simulation of complexitylib arithmetic circuits

The program below keeps every upstream wire at its original index. Each upstream constant gate
becomes a binary gate adding the given scalar to zero. Thus every designated output has a
project circuit of exactly the upstream size, even when multiple operands use the same gate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ComplexityLib

open Cslib.Circuits (Wire Line arithSignature arithInterpretationWith)

variable {K : Type*} {n g m : ℕ}

private def wireRef (w : Wire n g) : Ref K (Fin n) g :=
  w.elim Ref.var Ref.gate

private theorem read_wireRef {A : Type*} (scalar : K → A) (x : Fin n → A) (v : Fin g → A)
    (w : Wire n g) : (wireRef w).read scalar x v = w.elim x v := by
  cases w <;> rfl

variable [CommRing K]

private def appendLine (p : VPVNP.Program K (Fin n) g) :
    Line (arithSignature K) n g → VPVNP.Program K (Fin n) (g + 1)
  | ⟨.add, w⟩ => p.snoc .add (wireRef (w 0)) (wireRef (w 1))
  | ⟨.mul, w⟩ => p.snoc .mul (wireRef (w 0)) (wireRef (w 1))
  | ⟨.const k, _⟩ => p.snoc .add (.const k) (.const 0)

private def ofProgram : {g : ℕ} → Cslib.Circuits.Program (arithSignature K) n g →
    VPVNP.Program K (Fin n) g
  | _, .empty => .nil
  | _, .gate p line => appendLine (ofProgram p) line

private theorem run_ofProgram (p : Cslib.Circuits.Program (arithSignature K) n g) :
    (ofProgram p).run MvPolynomial.C MvPolynomial.X =
      p.eval (arithInterpretationWith K MvPolynomial.C) MvPolynomial.X := by
  induction p with
  | empty => rfl
  | gate p line ih =>
    obtain ⟨op, w⟩ := line
    cases op with
    | add | mul =>
      simp only [ofProgram, appendLine, VPVNP.Program.run, Cslib.Circuits.Program.eval,
        Line.eval, arithInterpretationWith, BinOp.apply, read_wireRef, Function.comp_apply, ih]
    | const k =>
      simp only [ofProgram, appendLine, VPVNP.Program.run, Cslib.Circuits.Program.eval,
        Line.eval, arithInterpretationWith, BinOp.apply, Ref.read, map_zero, add_zero, ih]

/-- An upstream arithmetic circuit has a project circuit for each designated output with
the same number of gates, evaluated in the formal polynomial ring. -/
theorem circuitSize_le_upstream (c : Cslib.Circuits.Circuit (arithSignature K) n m)
    (j : Fin m) : circuitSize (c.polynomial j) ≤ c.size := by
  let d : VPVNP.Circuit K (Fin n) c.size := ⟨ofProgram c.program, wireRef (c.outputs j)⟩
  have hd : d.polynomial = c.polynomial j := by
    simp only [d, Circuit.polynomial, Circuit.eval, read_wireRef, run_ofProgram]
    rfl
  rw [← hd]
  exact circuitSize_le_of_circuit d

end ComplexityLib

end VPVNP
end Computability
end OAI

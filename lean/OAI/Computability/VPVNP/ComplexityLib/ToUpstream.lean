import Complexity.Computability.Circuit.Arithmetic.VP
import OAI.Computability.VPVNP.CircuitSize

/-! # Simulating exact arithmetic circuits in complexitylib

The induction synthesizes all earlier gates at once, so two references to the
same gate can use the same wire. A binary gate needs at most two additional
gates for its scalar operands. Subtraction uses a constant gate for `-1`,
a multiplication, and an addition. A scalar output needs one final gate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ComplexityLib

open Cslib.Circuits (arithInterpretationWith arithSignature inputs Synthesis)
open MvPolynomial (C X)

variable {K : Type*} [CommRing K] {n g : ℕ}

/-- A polynomial-valued function of the input wires. -/
private abbrev WireFunction (K : Type*) [CommRing K] (n : ℕ) :=
  (Fin n → MvPolynomial (Fin n) K) → MvPolynomial (Fin n) K

/-- The polynomial-valued functions realized by the gates of a program prefix. -/
private def gateFunctions (p : Program K (Fin n) g) : Set (WireFunction K n) :=
  Set.range fun i x => p.run C x i

/-- Inputs and previously computed gates are available wires. A scalar
operand needs at most one new gate. -/
private theorem synthesizeRef (p : Program K (Fin n) g) (r : Ref K (Fin n) g) :
    Synthesis (arithInterpretationWith K C) (inputs n ∪ gateFunctions p)
      {fun x => r.read C x (p.run C x)} 1 := by
  cases r with
  | var i =>
    have hi : (fun x : Fin n → MvPolynomial (Fin n) K => x i) ∈ inputs n := ⟨i, rfl⟩
    exact (Synthesis.of_mem (Set.mem_union_left _ hi)).mono
      Set.Subset.rfl Set.Subset.rfl (by decide)
  | gate i =>
    have hi : (fun x => p.run C x i) ∈ gateFunctions p := ⟨i, rfl⟩
    exact (Synthesis.of_mem (Set.mem_union_right _ hi)).mono
      Set.Subset.rfl Set.Subset.rfl (by decide)
  | const k => exact Synthesis.arith_const k

/-- With the operands available, subtraction costs three gates and the other
two binary operations cost one. -/
private theorem synthesizeBinOp (op : BinOp) (a b : WireFunction K n) :
    Synthesis (arithInterpretationWith K C) {a, b}
      {fun x => op.apply (a x) (b x)} 3 := by
  have ha : a ∈ ({a, b} : Set (WireFunction K n)) := Set.mem_insert _ _
  have hb : b ∈ ({a, b} : Set (WireFunction K n)) := Set.mem_insert_of_mem _ rfl
  cases op with
  | add =>
    exact (Synthesis.arith_add ha hb).mono Set.Subset.rfl Set.Subset.rfl (by decide)
  | mul =>
    exact (Synthesis.arith_mul ha hb).mono Set.Subset.rfl Set.Subset.rfl (by decide)
  | sub =>
    have hneg : Synthesis (arithInterpretationWith K C) {a, b}
        {fun x => C (-1 : K) * b x} 2 :=
      (Synthesis.arith_const (-1 : K)).trans
        (Synthesis.arith_mul (Set.mem_union_right _ rfl) (Set.mem_union_left _ hb))
    simpa only [BinOp.apply, map_neg, map_one, neg_one_mul, sub_eq_add_neg] using
      hneg.trans (Synthesis.arith_add (Set.mem_union_left _ ha) (Set.mem_union_right _ rfl))

/-- The upstream program retains every gate of the simulated prefix at a cost
of at most five upstream gates per project gate. -/
private theorem synthesizeProgram (p : Program K (Fin n) g) :
    Synthesis (arithInterpretationWith K C) (inputs n) (gateFunctions p) (5 * g) := by
  induction p with
  | nil =>
    apply Synthesis.of_subset
    rintro _ ⟨i, _⟩
    exact i.elim0
  | @snoc g p op a b ih =>
    have step := (synthesizeRef p a).combine (synthesizeRef p b)
      (synthesizeBinOp op _ _)
    refine (ih.comp step).mono Set.Subset.rfl ?_ (by omega)
    rintro _ ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · apply Set.mem_union_right
      simp only [Program.run, Fin.lastCases_last, Set.mem_singleton_iff]
    · apply Set.mem_union_left
      exact ⟨j, by simp only [Program.run, Fin.lastCases_castSucc]⟩

/-- Every formal polynomial has an upstream circuit whose charged constants
and subtraction expansions cost at most five gates per project binary gate,
plus one gate if the designated output is a scalar. -/
theorem exists_upstream_circuit (p : MvPolynomial (Fin n) K) :
    ∃ c : Cslib.Circuits.Circuit (arithSignature K) n 1,
      c.polynomial 0 = p ∧ c.size ≤ 5 * circuitSize p + 1 := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  obtain ⟨d, hd, hsize⟩ := ((synthesizeProgram c.program).trans
    (synthesizeRef c.program c.output)).exists_circuit_polynomial
  exact ⟨d, hd.trans hc, hsize⟩

end ComplexityLib

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.CircuitSize
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Ideal.Operations

namespace OAI
/-! # Balanced-degree generators from the gates of an arithmetic circuit -/

namespace Hierarchy

open Computability.VPVNP MvPolynomial

def balancedCircuitTerms (d s : ℕ) : ℕ := (3*s+1)*(d+1)

namespace CircuitSplit

variable {F σ : Type*} [Field F] {n : ℕ}
noncomputable section

def operand (p : Program F σ n) (a : Ref F σ n) : MvPolynomial σ F :=
  a.read C X (p.run C X)

/-- At every gate retain its left operand, right operand, and result. Repeated
values occupy different positions, bounded by the number of operations. -/
def gateValues : {n : ℕ} → Program F σ n → List (MvPolynomial σ F)
  | _, .nil => []
  | _, .snoc p op a b =>
    operand p a :: operand p b :: op.apply (operand p a) (operand p b) :: gateValues p

@[simp] theorem length_gateValues (p : Program F σ n) : (gateValues p).length = 3*n := by
  induction p with
  | nil => rfl
  | snoc p op a b ih => simp only [gateValues, List.length_cons, ih]; omega

/-- Inactive positions and degrees are padded with a homogeneous zero.
All other positions contain a genuine component of one of the circuit values. -/
def generator (values : List (MvPolynomial σ F)) (d s : ℕ)
    (i : Fin (balancedCircuitTerms d s)) : MvPolynomial σ F :=
  let kj : Fin (3*s+1) × Fin (d+1) := finProdFinEquiv.symm i
  let j := kj.2.val
  if d < 3*j ∧ 3*j ≤ 2*d then
    homogeneousComponent j (values[kj.1.val]?.getD 0)
  else 0

theorem generator_balanced (values : List (MvPolynomial σ F)) {d s : ℕ} (hd : 2 ≤ d)
    (i : Fin (balancedCircuitTerms d s)) :
    ∃ j, (generator values d s i).IsHomogeneous j ∧ d < 3*j ∧ 3*j ≤ 2*d := by
  let kj : Fin (3*s+1) × Fin (d+1) := finProdFinEquiv.symm i
  by_cases h : d < 3*kj.2.val ∧ 3*kj.2.val ≤ 2*d
  · refine ⟨kj.2.val, ?_, h⟩
    change (if d < 3*kj.2.val ∧ 3*kj.2.val ≤ 2*d then
      homogeneousComponent kj.2.val (values[kj.1.val]?.getD 0) else 0).IsHomogeneous kj.2.val
    rw [ite_eq_left h]
    exact homogeneousComponent_isHomogeneous ..
  · refine ⟨(d+1)/2, ?_, by omega, by omega⟩
    change (if d < 3*kj.2.val ∧ 3*kj.2.val ≤ 2*d then
      homogeneousComponent kj.2.val (values[kj.1.val]?.getD 0) else 0).IsHomogeneous _
    rw [ite_eq_right h]
    exact isHomogeneous_zero σ F _

theorem component_mem_span {values : List (MvPolynomial σ F)} {d s : ℕ}
    (room : values.length ≤ 3*s+1) {g : MvPolynomial σ F} (hg : g ∈ values)
    {j : ℕ} (lo : d < 3*j) (hi : 3*j ≤ 2*d) :
    homogeneousComponent j g ∈ Ideal.span (Set.range (generator values d s)) := by
  obtain ⟨k, hk, eq⟩ := List.getElem_of_mem hg
  let a : Fin (3*s+1) := ⟨k, hk.trans_le room⟩
  let b : Fin (d+1) := ⟨j, by omega⟩
  apply Ideal.subset_span
  refine ⟨finProdFinEquiv (a,b), ?_⟩
  simp [generator, a, b, lo, hi, List.getElem?_eq_getElem hk, eq]

end
end CircuitSplit
end Hierarchy

end OAI

import OAI.Computability.VPVNP.HardnessWeights
import OAI.Computability.VPVNP.HardnessAlternatives

/-!
# Boolean formulas with scalar and variable labels

Each selected bit contributes a scalar and, optionally, a single formal
variable. The accepted assignments of the formula index a sum of monomials.
Selector bits implement finite scalar linear combinations of these sums.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Hardness

open MvPolynomial HardnessCNF
open scoped Classical

/-- A Boolean formula whose true variables contribute a scalar and, optionally, a polynomial
variable to the weight of an assignment. -/
structure MarkedCNF (F V : Type*) where
  /-- Number of Boolean variables in the marked formula. -/
  width : ℕ
  /-- The clauses selecting the assignments whose weights enter the polynomial. -/
  clauses : CNF width
  /-- Coefficient factor contributed when a given Boolean variable is true. -/
  scalar : Fin width → F
  /-- Optional polynomial variable contributed when a given Boolean variable is true. -/
  label : Fin width → Option V

namespace MarkedCNF

variable {F V : Type*} [CommSemiring F]

/-- The formal polynomial specified by the selected scalar and variable labels. -/
noncomputable def value (m : MarkedCNF F V) : MvPolynomial V F :=
  weightedCNF m.clauses (fun i => C (m.scalar i) * (m.label i).elim 1 X)

/-- The empty CNF with no Boolean variables has a single assignment of weight one. -/
def unit (F V : Type*) : MarkedCNF F V := ⟨0, [], Fin.elim0, Fin.elim0⟩

@[simp] theorem value_unit : (unit F V).value = 1 := by
  have hs (x : Fin 0 → Bool) : Satisfies [] x := fun _ h => nomatch h
  have hp (x : Fin 0 → Bool) :
      (∏ i : Fin 0, if x i then C (i.elim0 : F) * (i.elim0 : Option V).elim 1 X else 1) = 1 :=
    Finset.prod_eq_one fun i _ => i.elim0
  change weightedCNF ([] : CNF 0)
    (fun i => C (i.elim0 : F) * (i.elim0 : Option V).elim 1 X) = 1
  simp only [weightedCNF, hs, ite_true, hp]
  simp

variable {I : Type*} [Fintype I]

/-- The selector for a summand carries that summand's scalar. All data bits
retain the scalar and optional variable of the corresponding private block. -/
noncomputable def linearCombination (a : I → F) (m : I → MarkedCNF F V) :
    MarkedCNF F V where
  width := HardnessAlternatives.width (fun i => (m i).width)
  clauses := HardnessAlternatives.formula (fun i => (m i).clauses)
  scalar := HardnessAlternatives.weight _ a (fun i => (m i).scalar)
  label := HardnessAlternatives.weight _ (fun _ => none) (fun i => (m i).label)

theorem value_linearCombination (a : I → F) (m : I → MarkedCNF F V) :
    (linearCombination a m).value = ∑ i, C (a i) * (m i).value := by
  let k := fun i => (m i).width
  have hweight (j : Fin (HardnessAlternatives.width k)) :
      C ((linearCombination a m).scalar j) *
        ((linearCombination a m).label j).elim 1 X =
        HardnessAlternatives.weight k (fun i => C (a i))
          (fun i j => C ((m i).scalar j) * ((m i).label j).elim 1 X) j := by
    obtain ⟨s, rfl⟩ := (HardnessAlternatives.index k).surjective j
    rcases s with i | ⟨i, j⟩ <;> simp [linearCombination, k]
  change weightedCNF (HardnessAlternatives.formula fun i => (m i).clauses)
      (fun j => C ((linearCombination a m).scalar j) *
        ((linearCombination a m).label j).elim 1 X) = _
  rw [funext hweight]
  exact HardnessAlternatives.weighted_formula (fun i => (m i).clauses) (fun i => C (a i))
    (fun i j => C ((m i).scalar j) * ((m i).label j).elim 1 X)

end MarkedCNF
end Hardness

end VPVNP
end Computability
end OAI

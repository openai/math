import OAI.Computability.VPVNP.PermanentExpandedTerm
import OAI.Computability.VPVNP.PermanentGraphRows
import OAI.Computability.VPVNP.PermanentPortProduct
import OAI.Computability.VPVNP.PermanentEntryProduct
import OAI.Computability.VPVNP.PermanentClauseChoices

/-!
# The squarefree interior coefficient of a cycle-cover term

Once the directions of the ring rows and the choices of the clause rows
are fixed, each occurrence gadget sees two incoming bits. Its internal
rows cancel unless these bits agree. When they agree, the coefficient
retains the two exit columns precisely for the selected occurrence.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial
open scoped Classical

variable {k m c : ℕ} {R : Type*} [CommRing R]

theorem rowProduct_eq_expandedSum (occ : Fin m → Fin k × Fin c × Bool) (w : Fin k → R)
    (b : R) :
    sumAlgEquiv R (Interior m) (Exterior k m c) (rowProduct (graphMatrix occ w b)) =
      ∑ a : RingRow k m → Bool, ∑ y : Fin c → Fin m, expandedTerm occ w b a y := by
  rw [rowProduct_split]
  simp only [Fintype.prod_sum, Finset.mul_sum, Finset.sum_mul, expandedTerm]
  exact Finset.sum_comm

private theorem rearrange {A : Type*} [CommMonoid A] (g s d v z : A) :
    g * (s * (d * v)) * z = (s * d) * (g * v * z) := by ac_rfl

/-- Extracting the interior coefficient enforces both occurrence ownership and
agreement between the two incoming ports. -/
theorem coeff_expandedTerm (occ : Fin m → Fin k × Fin c × Bool) (w : Fin k → R)
    (b : R) (hb : -2 * b = 1) (a : RingRow k m → Bool) (y : Fin c → Fin m) :
    (expandedTerm occ w b a y).coeff (fullDegree (Interior m)) =
      if ownerOK occ y ∧
        (∀ g, a (markedPosition occ g) = (occ g).2.2 ↔ y (occ g).2.1 = g) then
        C (∏ u, ringWeight w u (a u)) *
          (directProduct occ a * ∏ g, if a (markedPosition occ g) = (occ g).2.2
            then X (ringExit occ g) * X (clauseExit occ g) else 1)
      else 0 := by
  by_cases hy : ownerOK occ y
  · let active (g : Fin m) := decide (a (markedPosition occ g) = (occ g).2.2)
    let picked (g : Fin m) := decide (y (occ g).2.1 = g)
    let scalar : MvPolynomial (Exterior k m c) R := C (∏ u, ringWeight w u (a u)) * directProduct occ a
    have hclause :
        (∏ i, if (occ (y i)).2.1 = i then X (y i, 1) else 0) =
          (∏ g, if picked g then X (g, (1 : Fin 3)) else 1 :
            MvPolynomial (Interior m) (MvPolynomial (Exterior k m c) R)) := by
      have own (i : Fin c) := hy i
      simp only [own, ite_true, picked, decide_eq_true_eq]
      exact prod_clause_ports y (fun g => (occ g).2.1) hy
        (fun g => (X (g, 1) : MvPolynomial (Interior m) (MvPolynomial (Exterior k m c) R)))
    have hweight :
        (∏ u, C (C (ringWeight w u (a u)))) =
          (C (C (∏ u, ringWeight w u (a u))) :
            MvPolynomial (Interior m) (MvPolynomial (Exterior k m c) R)) := by
      simp only [map_prod]
    have he :
        expandedTerm occ w b a y =
          C scalar * ((∏ g, rename (Prod.mk g)
            (equalityRows (C b) (X (ringExit occ g)) (X (clauseExit occ g)))) *
            (∏ g, if active g then X (g, (0 : Fin 3)) else 1) *
            (∏ g, if picked g then X (g, (1 : Fin 3)) else 1)) := by
      rw [expandedTerm, Finset.prod_mul_distrib, hweight, ringEntry_product, hclause]
      simp only [scalar, map_mul, active, decide_eq_true_eq]
      exact rearrange _ _ _ _ _
    have hb' : -2 * (C b : MvPolynomial (Exterior k m c) R) = 1 := by
      simpa [map_ofNat] using congrArg (C (σ := Exterior k m c)) hb
    have hagree : (∀ g, active g = picked g) ↔
        ∀ g, a (markedPosition occ g) = (occ g).2.2 ↔ y (occ g).2.1 = g := by
      simp [active, picked]
    rw [he, coeff_C_mul, coeff_portProduct _ hb']
    simp only [hagree, active, decide_eq_true_eq, hy, true_and, scalar]
    split_ifs <;> simp [mul_assoc]
  · have hbad : ∃ i, (occ (y i)).2.1 ≠ i := not_forall.mp hy
    obtain ⟨i, hi⟩ := hbad
    have hzero :
        (∏ j, if (occ (y j)).2.1 = j then X (y j, (1 : Fin 3)) else 0 :
            MvPolynomial (Interior m) (MvPolynomial (Exterior k m c) R)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [expandedTerm, hzero, hy]

end PermanentReduction

end VPVNP
end Computability
end OAI

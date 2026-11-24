import OAI.Computability.VPVNP.PermanentDirect
import OAI.Computability.VPVNP.PermanentExteriorDegree
import OAI.Computability.VPVNP.PermanentRegroup
import OAI.Computability.VPVNP.PermanentRingWeight

/-!
# Exterior columns after matching the two gadget ports

In a compatible choice, each occurrence used by its variable ring is also chosen
by its clause. Its two exits supply the missing ring and clause columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial
open scoped Classical

variable {k m c : ℕ} {R : Type*} [CommSemiring R]
variable (occ : Fin m → Fin k × Fin c × Bool) (a : RingRow k m → Bool)

/-- The exits of the active gadgets replace exactly the ring columns omitted
by the direct edges. -/
private theorem restore_ring_columns :
    directProduct (R := R) occ a *
        (∏ g, if a (markedPosition occ g) = (occ g).2.2 then X (ringExit occ g) else 1) =
      ∏ u, X (.inl (ringTarget u (a u))) := by
  let active (g : Fin m) := decide (a (markedPosition occ g) = (occ g).2.2)
  have hp (u : RingRow k m) (g : Fin m) :
      markedPort occ u (a u) = some g ↔ u = markedPosition occ g ∧ active g = true := by
    rw [markedPort_eq_some]
    simp only [active, decide_eq_true_eq]
    exact and_congr_right (fun h => h ▸ Iff.rfl)
  have hr := prod_optional_ports (fun u => markedPort occ u (a u)) (markedPosition occ)
    active hp (fun g => (X (ringExit occ g) : MvPolynomial (Exterior k m c) R))
  simp only [active, decide_eq_true_eq] at hr
  rw [← hr, directProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u _
  cases h : markedPort occ u (a u) with
  | none => simp
  | some g =>
    obtain ⟨hpos, hbit⟩ := (markedPort_eq_some occ u (a u) g).mp h
    simp [ringExit, ← hpos, ← hbit]

/-- A matched term uses every clause column once and the same ring columns as
the original ring assignment. -/
theorem matched_exterior_columns (y : Fin c → Fin m)
    (hy : ∀ z, (occ (y z)).2.1 = z)
    (hmatch : ∀ g, a (markedPosition occ g) = (occ g).2.2 ↔ y (occ g).2.1 = g) :
    directProduct (R := R) occ a *
      (∏ g, if a (markedPosition occ g) = (occ g).2.2
        then X (ringExit occ g) * X (clauseExit occ g) else 1) =
      (∏ u, X (.inl (ringTarget u (a u)))) * ∏ z : Fin c, X (.inr z) := by
  have hsplit :
      (∏ g, if a (markedPosition occ g) = (occ g).2.2
        then X (ringExit occ g) * X (clauseExit occ g) else 1) =
      (∏ g, if a (markedPosition occ g) = (occ g).2.2 then X (ringExit occ g) else 1) *
        (∏ g, if y (occ g).2.1 = g then (X (clauseExit occ g) : MvPolynomial (Exterior k m c) R)
          else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro g _
    by_cases h : a (markedPosition occ g) = (occ g).2.2
    · simp [h, (hmatch g).mp h]
    · simp [h, mt (hmatch g).mpr h]
  have hc := prod_clause_ports y (fun g => (occ g).2.1) hy
    (fun g => (X (clauseExit occ g) : MvPolynomial (Exterior k m c) R))
  rw [hsplit, ← mul_assoc, restore_ring_columns, ← hc]
  simp [clauseExit, hy]

/-- A matched term supplies the full exterior degree exactly for consistent rings. -/
theorem coeff_exterior_matched (y : Fin c → Fin m)
    (hy : ∀ z, (occ (y z)).2.1 = z)
    (hmatch : ∀ g, a (markedPosition occ g) = (occ g).2.2 ↔ y (occ g).2.1 = g) :
    (directProduct (R := R) occ a *
      (∏ g, if a (markedPosition occ g) = (occ g).2.2
        then X (ringExit occ g) * X (clauseExit occ g) else 1)).coeff
      (fullDegree (Exterior k m c)) = if ∀ v j, a (v, j) = a (v, 0) then 1 else 0 := by
  rw [matched_exterior_columns occ a y hy hmatch, coeff_ring_clause_columns]

end PermanentReduction

end VPVNP
end Computability
end OAI

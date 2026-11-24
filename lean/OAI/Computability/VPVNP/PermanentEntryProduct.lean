import OAI.Computability.VPVNP.PermanentDirect
import OAI.Computability.VPVNP.PermanentRegroup

/-!
# Separating exterior ring edges from occurrence ports

A ring row chooses either a direct edge to the next exterior column or an
edge to the first interior column of its occurrence gadget. Multiplying the
row choices uses each active occurrence port exactly once.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial

variable {R : Type*} [CommSemiring R] {k m c : ℕ}

/-- Under the variable-splitting equivalence, ring inputs factor into the
direct exterior product and one interior variable for each active occurrence. -/
theorem ringEntry_product (occ : Fin m → Fin k × Fin c × Bool) (a : RingRow k m → Bool) :
    (∏ u, sumAlgEquiv R (Interior m) (Exterior k m c) (X (ringEntry occ u (a u)))) =
      C (directProduct (R := R) occ a) *
        ∏ g, if a (markedPosition occ g) = (occ g).2.2 then X (g, (0 : Fin 3)) else 1 := by
  let pick (u : RingRow k m) := markedPort occ u (a u)
  let direct (u : RingRow k m) : MvPolynomial (Exterior k m c) R :=
    if (pick u).isSome then 1 else X (.inl (ringTarget u (a u)))
  let port (g : Fin m) : MvPolynomial (Interior m) (MvPolynomial (Exterior k m c) R) := X (g, 0)
  have entry (u : RingRow k m) :
      sumAlgEquiv R (Interior m) (Exterior k m c) (X (ringEntry occ u (a u))) =
        C (direct u) * (pick u).elim 1 port := by
    cases hp : markedPort occ u (a u) <;> simp [pick, direct, port, ringEntry, hp]
  have hpick (u : RingRow k m) (g : Fin m) :
      pick u = some g ↔ u = markedPosition occ g ∧ decide (a (markedPosition occ g) = (occ g).2.2) = true := by
    simp only [pick, decide_eq_true_eq, markedPort_eq_some]
    exact and_congr_right fun he => he ▸ Iff.rfl
  rw [Finset.prod_congr rfl (fun u _ => entry u), Finset.prod_mul_distrib, ← map_prod]
  congr 1
  simpa [port] using prod_optional_ports pick (markedPosition occ)
    (fun g => decide (a (markedPosition occ g) = (occ g).2.2)) hpick port

end PermanentReduction

end VPVNP
end Computability
end OAI

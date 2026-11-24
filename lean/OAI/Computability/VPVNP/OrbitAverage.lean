import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Uniform averaging on transitive finite group actions

Section 5 compares Grassmann pair energies by lifting them to the general
linear group. A uniformly chosen group element takes a fixed point of any
transitive finite action to a uniformly chosen point.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

/-- A finite group average of an observable agrees with its uniform average on a
transitive finite set. -/
theorem orbitAverage_eq_uniformAverage (G : Type*) {S : Type*} [Group G] [Fintype G]
    [Fintype S] [MulAction G S] [MulAction.IsPretransitive G S] (s : S) (E : S → ℝ) :
    (∑ g : G, E (g • s)) / Fintype.card G = (∑ x : S, E x) / Fintype.card S := by
  let : Nonempty S := ⟨s⟩
  have hx (x : S) : (∑ g : G, E (g • x)) = ∑ g : G, E (g • s) := by
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G s x
    simp_rw [smul_smul]
    exact Equiv.sum_comp (Equiv.mulRight h) (fun g : G ↦ E (g • s))
  have hg (g : G) : (∑ x : S, E (g • x)) = ∑ x : S, E x :=
    Equiv.sum_comp (MulAction.toPerm g) E
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).2
  calc
    _ = ∑ x : S, ∑ g : G, E (g • x) := by simp_rw [hx]; simp [mul_comm]
    _ = ∑ g : G, ∑ x : S, E (g • x) := Finset.sum_comm
    _ = _ := by simp_rw [hg]; simp [mul_comm]

end Grassmann

end VPVNP
end Computability
end OAI

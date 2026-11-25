import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! # Reflections of permutation cycles

On each orbit, the two reflections of integer exponents about 0 and about 1/2
compose to one forward step. The resulting global involutions give two stages
of disjoint transpositions on any finite set of bit positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

noncomputable section

variable {α : Type*} (σ : Equiv.Perm α)

private def orbitBase (x : α) : α :=
  (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x).out

private theorem sameCycle_base (x : α) : σ.SameCycle (orbitBase σ x) x :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x))

private theorem orbitBase_eq {x y : α} (h : σ.SameCycle x y) :
    orbitBase σ x = orbitBase σ y :=
  congrArg Quotient.out (Quotient.sound (s := Equiv.Perm.SameCycle.setoid σ) h)

private def orbitIndex (x : α) : ℤ := (sameCycle_base σ x).choose

private theorem orbitIndex_spec (x : α) : (σ ^ orbitIndex σ x) (orbitBase σ x) = x :=
  (sameCycle_base σ x).choose_spec

private theorem combinePowers (a b : ℤ) (x : α) :
    (σ ^ a) ((σ ^ b) x) = (σ ^ (a + b)) x := by
  rw [zpow_add]
  rfl

private def reflectOrbit (d : ℤ) (x : α) : α :=
  (σ ^ (d - orbitIndex σ x)) (orbitBase σ x)

private theorem reflectOrbit_of_power {x y : α} (d j : ℤ)
    (hj : (σ ^ j) (orbitBase σ x) = y) :
    reflectOrbit σ d y = (σ ^ (d - j)) (orbitBase σ x) := by
  have hbase := orbitBase_eq σ ((sameCycle_base σ x).symm.trans ⟨j, hj⟩)
  have h := orbitIndex_spec σ y
  rw [← hbase] at h
  have equal := congrArg (σ ^ (d - orbitIndex σ y - j)) (h.trans hj.symm)
  simp only [combinePowers] at equal
  unfold reflectOrbit
  rw [← hbase]
  rw [show d - orbitIndex σ y - j + j = d - orbitIndex σ y by omega,
    show d - orbitIndex σ y - j + orbitIndex σ y = d - j by omega] at equal
  exact equal.symm

private theorem reflectOrbit_involutive (d : ℤ) : Function.Involutive (reflectOrbit σ d) := by
  intro x
  rw [reflectOrbit_of_power σ (x := x) (y := reflectOrbit σ d x) d (d - orbitIndex σ x) rfl,
    sub_sub_cancel, orbitIndex_spec]

/-- Two successive involutions implement any permutation. Over a finite position
set, each involution exchanges disjoint pairs of positions simultaneously. -/
theorem exists_involutions_trans (σ : Equiv.Perm α) :
    ∃ r s : Equiv.Perm α, Function.Involutive r ∧ Function.Involutive s ∧ r.trans s = σ := by
  let R (d : ℤ) : Equiv.Perm α :=
    ⟨reflectOrbit σ d, reflectOrbit σ d, reflectOrbit_involutive σ d, reflectOrbit_involutive σ d⟩
  refine ⟨R 0, R 1, reflectOrbit_involutive σ 0, reflectOrbit_involutive σ 1, ?_⟩
  ext x
  change reflectOrbit σ 1 (reflectOrbit σ 0 x) = σ x
  rw [reflectOrbit_of_power σ (x := x) (y := reflectOrbit σ 0 x) 1 (0 - orbitIndex σ x) rfl]
  rw [show 1 - (0 - orbitIndex σ x) = 1 + orbitIndex σ x by omega, ← combinePowers,
    zpow_one, orbitIndex_spec]

end

end Controlled

end NearSquareRoot
end Computability
end OAI

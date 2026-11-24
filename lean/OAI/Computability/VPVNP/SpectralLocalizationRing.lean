import Mathlib.Algebra.Ring.Basic
import Mathlib.Basic.Countable.Basic
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Tactic.Abel

/-!
# Additive group completion for the spectral localization

We pass from a commutative semiring to a ring by forming formal differences.
Multiplication extends by additivity in each variable, even when addition in
the original semiring is noncancellative.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

noncomputable section

/-- The additive Grothendieck group of a semiring, equipped below with the induced ring structure. -/
def G (S : Type*) [CommSemiring S] := Algebra.GrothendieckAddGroup S
deriving AddCommGroup

variable {S : Type*} [CommSemiring S]

private abbrev incl : S →+ G S := Algebra.GrothendieckAddGroup.of

private theorem exists_sub_incl (z : G S) : ∃ a b : S, z = incl a - incl b := by
  obtain ⟨⟨a, b⟩, h⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid S)).surj z
  exact ⟨a, b, eq_sub_iff_add_eq.mpr h⟩

private def lift {A : Type*} [AddCommGroup A] (f : S →+ A) : G S →+ A :=
  Algebra.GrothendieckAddGroup.lift f

private theorem lift_incl {A : Type*} [AddCommGroup A] (f : S →+ A) (x : S) :
    lift f (incl x) = f x :=
  DFunLike.congr_fun (Algebra.GrothendieckAddGroup.lift.symm_apply_apply f) x

private def product : G S →+ G S →+ G S :=
  lift (lift ((AddMonoidHom.mul : S →+ S →+ S).compr₂ incl)).flip

private theorem product_incl (a b : S) : product (incl a) (incl b) = incl (a * b) := by
  unfold product
  rw [lift_incl]
  change lift ((AddMonoidHom.mul : S →+ S →+ S).compr₂ incl) (incl b) a = _
  rw [lift_incl]
  exact congrArg incl (mul_comm b a)

instance : CommRing (G S) where
  __ := (inferInstance : AddCommGroup (G S))
  mul := fun a b => product a b
  one := incl 1
  zero_mul a := DFunLike.congr_fun (map_zero product) a
  mul_zero a := map_zero (product a)
  left_distrib a b c := map_add (product a) b c
  right_distrib a b c := DFunLike.congr_fun (map_add product a b) c
  one_mul x := by
    change product (incl (1 : S)) x = x
    obtain ⟨a, b, rfl⟩ := exists_sub_incl x
    simp only [map_sub, product_incl, one_mul]
  mul_one x := by
    change product x (incl (1 : S)) = x
    obtain ⟨a, b, rfl⟩ := exists_sub_incl x
    simp only [map_sub, AddMonoidHom.sub_apply, product_incl, mul_one]
  mul_comm x y := by
    change product x y = product y x
    obtain ⟨a, b, rfl⟩ := exists_sub_incl x
    obtain ⟨c, d, rfl⟩ := exists_sub_incl y
    simp only [map_sub, AddMonoidHom.sub_apply, product_incl, mul_comm a, mul_comm b]
    abel
  mul_assoc x y z := by
    change product (product x y) z = product x (product y z)
    obtain ⟨a, b, rfl⟩ := exists_sub_incl x
    obtain ⟨c, d, rfl⟩ := exists_sub_incl y
    obtain ⟨e, f, rfl⟩ := exists_sub_incl z
    simp only [map_sub, AddMonoidHom.sub_apply, product_incl, mul_assoc]

/-- The canonical semiring homomorphism to the ring of differences. -/
def toG : S →+* G S where
  __ := incl
  map_one' := rfl
  map_mul' a b := (product_incl a b).symm

/-- Two generators agree exactly when adding a common semiring element makes them equal. -/
theorem toG_eq_iff (a b : S) : toG a = toG b ↔ ∃ w : S, a + w = b + w := by
  change AddLocalization.addMonoidOf ⊤ a = AddLocalization.addMonoidOf ⊤ b ↔ _
  rw [AddSubmonoid.LocalizationMap.eq_iff_exists]
  simp [add_comm a, add_comm b]

/-- Every element of the completion is a difference of two generators. -/
theorem exists_sub (z : G S) : ∃ a b : S, z = toG a - toG b := exists_sub_incl z

instance [Countable S] : Countable (G S) := by
  apply Function.Surjective.countable (f := fun p : S × S => toG p.1 - toG p.2)
  intro z
  obtain ⟨a, b, h⟩ := exists_sub z
  exact ⟨(a, b), h.symm⟩

end

end Spectral

end VPVNP
end Computability
end OAI

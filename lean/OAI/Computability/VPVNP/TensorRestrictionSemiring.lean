import OAI.Computability.VPVNP.TensorRestriction
import OAI.Computability.VPVNP.TensorDistributivity
import OAI.Computability.VPVNP.TensorUnitLaws
import OAI.Computability.VPVNP.WireSpectrum
import OAI.Computability.VPVNP.SpectralLocalizationCone

/-!
# The restriction semiring on a finite party set

The direct sum and parallel tensor product of arrays make their mutual
restriction classes into a commutative semiring. The natural number `n`
is represented by the all-party diagonal with `n` entries. A nonzero array
restricts to the unit, and the product of its local dimensions gives a
natural number that restricts to the array. These are the order bounds
used in Appendix A.1 of *VP and VNP differ over every field*.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.RestrictionClass

universe u v

variable {k : Type u} {J : Type v} [Field k] [Fintype J] [Nonempty J]

private theorem add_swap (a b : RestrictionClass k J) : a + b = b + a :=
  Quotient.inductionOn₂ a b fun T U => Quotient.sound (directSum_comm_mutual T U)

omit [Nonempty J] in
private theorem mul_swap (a b : RestrictionClass k J) : a * b = b * a :=
  Quotient.inductionOn₂ a b fun T U => Quotient.sound (tensorProduct_comm_mutual T U)

private theorem mul_distrib (a b c : RestrictionClass k J) :
    a * (b + c) = a*b + a*c :=
  Quotient.inductionOn₃ a b c fun T U V => Quotient.sound (tensorProduct_directSum_mutual T U V)

private theorem diagonal_succ (n : ℕ) :
    (ofTensor (diagonal (Fin (n+1))) : RestrictionClass k J) = ofTensor (diagonal (Fin n)) + 1 := by
  calc
    _ = ofTensor (diagonal (Fin n ⊕ Fin 1)) :=
      (ofTensor_eq_iff _ _).2 (diagonal_reindex_mutual finSumFinEquiv.symm)
    _ = ofTensor (directSum (diagonal (Fin n)) (diagonal (Fin 1))) :=
      (ofTensor_eq_iff _ _).2 (diagonal_sum_mutual _ _)
    _ = _ := congrArg (ofTensor (diagonal (Fin n)) + ·) ((ofTensor_eq_iff _ _).2 diagonal_unit_mutual)

noncomputable instance : CommSemiring (RestrictionClass k J) where
  nsmul := nsmulRec
  natCast n := ofTensor (diagonal (Fin n))
  natCast_zero := rfl
  natCast_succ := diagonal_succ
  add_assoc a b c := Quotient.inductionOn₃ a b c fun T U V => Quotient.sound (directSum_assoc_mutual T U V)
  add_comm := add_swap
  add_zero a := Quotient.inductionOn a fun T => Quotient.sound (directSum_zero_mutual T)
  zero_add a := (add_swap 0 a).trans (Quotient.inductionOn a fun T => Quotient.sound (directSum_zero_mutual T))
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun T U V => Quotient.sound (tensorProduct_assoc_mutual T U V)
  mul_comm := mul_swap
  mul_one a := Quotient.inductionOn a fun T => Quotient.sound (tensorProduct_unit_mutual T)
  one_mul a := (mul_swap 1 a).trans (Quotient.inductionOn a fun T => Quotient.sound (tensorProduct_unit_mutual T))
  mul_zero a := Quotient.inductionOn a fun T => Quotient.sound (tensorProduct_zero_mutual T)
  zero_mul a := (mul_swap 0 a).trans (Quotient.inductionOn a fun T => Quotient.sound (tensorProduct_zero_mutual T))
  left_distrib := mul_distrib
  right_distrib a b c := by rw [mul_swap (a+b), mul_distrib, mul_swap c a, mul_swap c b]

@[simp] theorem ofTensor_diagonal_fin (n : ℕ) :
    ofTensor (diagonal (Fin n)) = (n : RestrictionClass k J) := rfl

@[simp] theorem ofTensor_eq_zero_iff (T : Tensor.{u,v,0} k J) :
    ofTensor T = 0 ↔ T.coeff = 0 := by
  change ofTensor T = ofTensor (diagonal (Fin 0)) ↔ _
  rw [ofTensor_eq_iff, zero_restricts_iff, and_iff_right (restricts_zero T)]

instance : Nontrivial (RestrictionClass k J) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have hz := (ofTensor_eq_zero_iff (k := k) (J := J) unit).1 h
  exact one_ne_zero (α := k) (congrFun hz (fun _ => PUnit.unit))

/-- Nonzero coefficient witnesses in the two factors combine into one in their product. -/
instance : NoZeroDivisors (RestrictionClass k J) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective a
    obtain ⟨U, rfl⟩ := ofTensor_surjective b
    rw [← ofTensor_tensorProduct, ofTensor_eq_zero_iff, ofTensor_eq_zero_iff, ofTensor_eq_zero_iff]
    contrapose!
    rintro ⟨hT, hU⟩
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hT
    obtain ⟨y, hy⟩ := Function.ne_iff.mp hU
    exact Function.ne_iff.mpr ⟨fun j => (x j, y j), mul_ne_zero hx hy⟩

/-- Rank bounds and monotonicity under independent restrictions supply all
the order hypotheses of strict spectral comparison. -/
theorem orderBounds : Spectral.OrderBounds (RestrictionClass k J) where
  zero_le a := Quotient.inductionOn a restricts_zero
  one_le {a} := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective a
    exact fun h => restricts_unit_of_ne_zero T (fun hT => h ((ofTensor_eq_zero_iff T).2 hT))
  bounded a := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective a
    exact ⟨_, diagonal_restricts_of_card T⟩
  add_mono {a b c d} := by
    obtain ⟨A, rfl⟩ := ofTensor_surjective a
    obtain ⟨B, rfl⟩ := ofTensor_surjective b
    obtain ⟨C, rfl⟩ := ofTensor_surjective c
    obtain ⟨D, rfl⟩ := ofTensor_surjective d
    exact fun h g => directSum_restricts h g
  mul_mono t {a b} := by
    obtain ⟨T, rfl⟩ := ofTensor_surjective t
    obtain ⟨A, rfl⟩ := ofTensor_surjective a
    obtain ⟨B, rfl⟩ := ofTensor_surjective b
    exact fun h => (Restricts.refl T).tensorProduct h

end WireTensor.RestrictionClass

end VPVNP
end Computability
end OAI

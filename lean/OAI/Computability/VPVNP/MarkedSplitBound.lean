import OAI.Computability.VPVNP.MarkedSplitIdentity

/-!
# Cost of the two orders of a marked-index operator

Appendix A.2 places the exterior column and row at fixed endpoints, with an
old index and a newly exposed index. The two matrix orders pair these four
roles in opposite ways. Local restriction first realizes the factorization
and then contracts the old index against the background tensor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.SpectralPoint

variable {k J : Type*} [Field k] [Fintype J]

private def operatorSide (reverse : Bool) : Option (Option Bool) → Bool
  | none => !reverse
  | some none => reverse
  | some (some side) => side

private theorem value_wire_card (F : SpectralPoint k J) (a b : J)
    (I : Type) [Fintype I] [Nonempty I] :
    (F.value (wire a b I) : ℝ) = (Fintype.card I : ℝ) ^ F.wireDistance a b := by
  rw [F.value_wire_equiv a b (Fintype.equivFin I)]
  exact F.value_wire_eq_rpow a b Fintype.card_pos

private theorem value_splitMarkedTerm_le_factor (F : SpectralPoint k J)
    (B : J → Type) [∀ j, Fintype (B j)] (I H K : Type) [Fintype I] [Fintype H] [Fintype K]
    (x a b old : J) (T : ((j : J) → B j) → I → k) (M : I → I → H → H → k)
    (side : Option (Option Bool) → Bool) (center : Bool → J)
    (L : ((r : Option (Option Bool)) → side r = false → cutBasis (tripleBasis I H) I r) → K → k)
    (D : ((r : Option (Option Bool)) → side r = true → cutBasis (tripleBasis I H) I r) → K → k)
    (h : ∀ t : (r : Option (Option Bool)) → cutBasis (tripleBasis I H) I r,
      M (t (some none)) (t none) (t (some (some true))) (t (some (some false))) =
        ∑ z, L (fun r _ ↦ t r) z * D (fun r _ ↦ t r) z) :
    F.value (splitMarkedTerm B I H x a b T M) ≤
      F.value (marked B I old T) * (F.value (wire (center false) (center true) K) *
        ∏ r : Option (Option Bool), F.value (wire (r.elim old (triplePlace x a b))
          (center (side r)) (cutBasis (tripleBasis I H) I r))) := by
  let A (t : (r : Option Bool) → tripleBasis I H r) (j : I) :=
    M (t none) j (t (some true)) (t (some false))
  let op := placedTensor (fun r ↦ r.elim old (triplePlace x a b)) (cutBasis (tripleBasis I H) I)
    (fun t ↦ A (fun r ↦ t (some r)) (t none))
  have he : F.value (splitMarkedTerm B I H x a b T M) ≤ F.value (marked B I old T) * F.value op := by
    rw [← F.value_tensorProduct]
    exact F.monotone (contract_marked_operator B (tripleBasis I H) I old (triplePlace x a b) T A)
  refine he.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
  have hh := F.value_cutFactorization_le (fun r ↦ r.elim old (triplePlace x a b)) side center
    (cutBasis (tripleBasis I H) I) K L D
  convert hh using 2
  apply congrArg _
  funext t
  exact h _

/-- The old index pairs with the row, and the new index pairs with the column. -/
theorem value_splitMarkedTerm_le_plus (F : SpectralPoint k J) (B : J → Type) [∀ j, Fintype (B j)]
    (I H K : Type) [Fintype I] [Fintype H] [Fintype K] [Nonempty I] [Nonempty H] [Nonempty K]
    (x a b old : J) (T : ((j : J) → B j) → I → k) (M : I → I → H → H → k)
    (L D : I → H → K → k) (h : ∀ i j β α, M i j β α = ∑ z, L i α z * D j β z) :
    (F.value (splitMarkedTerm B I H x a b T M) : ℝ) ≤ F.value (marked B I old T) *
      ((Fintype.card K : ℝ) ^ F.wireDistance x old * (Fintype.card H : ℝ) ^ F.wireDistance a x *
        (Fintype.card H : ℝ) ^ F.wireDistance b old) := by
  let center := fun s : Bool ↦ if s then old else x
  have bound := value_splitMarkedTerm_le_factor F B I H K x a b old T M (operatorSide false) center
    (fun t ↦ L (t (some none) rfl) (t (some (some false)) rfl))
    (fun t ↦ D (t none rfl) (t (some (some true)) rfl))
    (fun t ↦ h _ _ _ _)
  rw [Fintype.prod_option, Fintype.prod_option, Fintype.prod_bool] at bound
  change F.value _ ≤ F.value _ * (F.value (wire x old K) * (F.value (wire old old I) *
    (F.value (wire x x I) * (F.value (wire b old H) * F.value (wire a x H))))) at bound
  have bound' := NNReal.coe_le_coe.mpr bound
  simpa only [NNReal.coe_mul, value_wire_card, F.wireDistance_self, Real.rpow_zero,
    one_mul, mul_assoc, mul_left_comm, mul_comm] using bound'

/-- The old index pairs with the column, and the new index pairs with the row. -/
theorem value_splitMarkedTerm_le_minus (F : SpectralPoint k J) (B : J → Type) [∀ j, Fintype (B j)]
    (I H K : Type) [Fintype I] [Fintype H] [Fintype K] [Nonempty I] [Nonempty H] [Nonempty K]
    (x a b old : J) (T : ((j : J) → B j) → I → k) (M : I → I → H → H → k)
    (L D : I → H → K → k) (h : ∀ i j β α, M i j β α = ∑ z, L j α z * D i β z) :
    (F.value (splitMarkedTerm B I H x a b T M) : ℝ) ≤ F.value (marked B I old T) *
      ((Fintype.card K : ℝ) ^ F.wireDistance old x * (Fintype.card H : ℝ) ^ F.wireDistance a old *
        (Fintype.card H : ℝ) ^ F.wireDistance b x) := by
  let center := fun s : Bool ↦ if s then x else old
  have bound := value_splitMarkedTerm_le_factor F B I H K x a b old T M (operatorSide true) center
    (fun t ↦ L (t none rfl) (t (some (some false)) rfl))
    (fun t ↦ D (t (some none) rfl) (t (some (some true)) rfl))
    (fun t ↦ h _ _ _ _)
  rw [Fintype.prod_option, Fintype.prod_option, Fintype.prod_bool] at bound
  change F.value _ ≤ F.value _ * (F.value (wire old x K) * (F.value (wire old old I) *
    (F.value (wire x x I) * (F.value (wire b x H) * F.value (wire a old H))))) at bound
  have bound' := NNReal.coe_le_coe.mpr bound
  simpa only [NNReal.coe_mul, value_wire_card, F.wireDistance_self, Real.rpow_zero,
    one_mul, mul_assoc, mul_left_comm, mul_comm] using bound'

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI

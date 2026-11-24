import OAI.Computability.VPVNP.MarkedRelocation
import OAI.Computability.VPVNP.SpectralGeometry

/-!
# Transporting two marked tensor indices

The two marked factors in Appendix A.3 may be placed at coincident parties.
To relocate one of them, keep the other as part of the background basis.
The two regroupings preserve every coefficient.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

open scoped Classical

universe u v
variable {k : Type u} {J : Type v} (B : J → Type) [∀ j, Fintype (B j)]
    (I K : Type) [Fintype I] [Fintype K]
    (T : ((j : J) → B j) → I → K → k)

/-- An array with a marked row at `a` and a marked column at `b`. -/
noncomputable def twoMarked (a b : J) : Tensor k J where
  Basis j := B j × (j = a → I) × (j = b → K)
  finiteBasis _ := inferInstance
  coeff x := T (fun j ↦ (x j).1) ((x a).2.1 rfl) ((x b).2.2 rfl)

/-- View the second marked leg as part of the background. -/
def holdSecond (b : J) (x : (j : J) → B j × (j = b → K)) (i : I) : k :=
  T (fun j ↦ (x j).1) i ((x b).2 rfl)

/-- View the first marked leg as part of the background. -/
def holdFirst (a : J) (x : (j : J) → B j × (j = a → I)) (j : K) : k :=
  T (fun t ↦ (x t).1) ((x a).2 rfl) j

theorem twoMarked_coeff_eq_zero_iff [Zero k] (a b : J) :
    (twoMarked B I K T a b).coeff = 0 ↔ T = 0 := by
  constructor
  · intro h
    funext x i j
    exact congrFun h (fun t ↦ (x t, fun _ ↦ i, fun _ ↦ j))
  · intro h
    subst T
    rfl

variable [Fintype J] [Field k]

theorem twoMarked_first_mutual (a b : J) :
    let P := twoMarked B I K T a b
    let U := marked (fun j ↦ B j × (j = b → K)) I a (holdSecond B I K T b)
    Restricts P U ∧ Restricts U P := by
  let e (j : J) : (B j × (j = b → K)) × (j = a → I) ≃ B j × (j = a → I) × (j = b → K) :=
    { toFun x := (x.1.1, x.2, x.1.2)
      invFun x := ((x.1, x.2.2), x.2.1)
      left_inv _ := rfl
      right_inv _ := rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

theorem twoMarked_second_mutual (a b : J) :
    let P := twoMarked B I K T a b
    let U := marked (fun j ↦ B j × (j = a → I)) K b (holdFirst B I K T a)
    Restricts P U ∧ Restricts U P := by
  exact restricts_of_reindex
    (fun j ↦ Equiv.prodAssoc (B j) (j = a → I) (j = b → K)) (fun _ ↦ rfl)

/-- With trivial background and the identity coefficient table, the two
marked legs give the equality wire at their chosen parties. -/
theorem twoMarked_wire_mutual (a b : J) :
    let W := twoMarked (fun _ : J ↦ Unit) I I (fun _ i j ↦ if i = j then (1 : k) else 0) a b
    Restricts W (wire a b I) ∧ Restricts (wire a b I) W := by
  let e (j : J) : (j = a → I) × (j = b → I) ≃ Unit × (j = a → I) × (j = b → I) :=
    { toFun x := ((), x)
      invFun x := x.2
      left_inv _ := rfl
      right_inv _ := rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

/-- Combining first-index and second-index relocation bounds gives the four
independent endpoint weights of (A.4). -/
theorem twoMarked_independent_bound (F : SpectralPoint k J)
    (a b : Bool → J) (c d : J) {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (first : (F.value (twoMarked B I K T c d) : ℝ) ≤
      (F.value (twoMarked B I K T (a false) d) : ℝ) ^ (1-u) *
      (F.value (twoMarked B I K T (a true) d) : ℝ) ^ u)
    (second : ∀ i, (F.value (twoMarked B I K T (a i) d) : ℝ) ≤
      (F.value (twoMarked B I K T (a i) (b false)) : ℝ) ^ (1-v) *
      (F.value (twoMarked B I K T (a i) (b true)) : ℝ) ^ v) :
    (F.value (twoMarked B I K T c d) : ℝ) ≤ ∏ i : Bool, ∏ j : Bool,
      (F.value (twoMarked B I K T (a i) (b j)) : ℝ) ^
        ((SpectralGeometry.independentCoupling hu hv).mass i j) := by
  have h₀ := Real.rpow_le_rpow (by positivity) (second false) (sub_nonneg.mpr hu.2)
  have h₁ := Real.rpow_le_rpow (by positivity) (second true) hu.1
  have h := first.trans (mul_le_mul h₀ h₁ (by positivity) (by positivity))
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)] at h
  simp only [Fintype.prod_bool, SpectralGeometry.independentCoupling, Bool.false_eq_true,
    ↓reduceIte]
  simpa only [mul_comm, mul_assoc, mul_left_comm] using h

/-- Equation (A.4). Relocation of each mark bounds the value at the two
fractional points by the independent product of all four endpoint values. -/
theorem SpectralPoint.value_twoMarked_atFraction_le (F : SpectralPoint k J)
    (a b : Bool → J) (c d : J) {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hc : @WireGeometry.AtFraction _ F.wirePseudoMetric (a false) (a true) u c)
    (hd : @WireGeometry.AtFraction _ F.wirePseudoMetric (b false) (b true) v d) :
    (F.value (twoMarked B I K T c d) : ℝ) ≤ ∏ i : Bool, ∏ j : Bool,
      (F.value (twoMarked B I K T (a i) (b j)) : ℝ) ^
        ((SpectralGeometry.independentCoupling hu hv).mass i j) := by
  apply twoMarked_independent_bound B I K T F a b c d hu hv
  · simp only [F.value_eq_of_mutual (twoMarked_first_mutual B I K T _ d)]
    exact F.value_marked_atFraction_le _ I _ _ _ _ hu.1 hu.2 hc
  · intro i
    simp only [F.value_eq_of_mutual (twoMarked_second_mutual B I K T (a i) _)]
    exact F.value_marked_atFraction_le _ K _ _ _ _ hv.1 hv.2 hd

end WireTensor

end VPVNP
end Computability
end OAI

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# The crossing tensor on the signed coordinate axes

A coordinate at either end of a diameter is an `m`-bit string. The tensor
`C_{D,m}` tests equality on each of the `D` diameters independently. Its
single coordinate at the center represents the trivial leg.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Crossing

open scoped BigOperators

abbrev BitString (m : ℕ) := Fin m → Bool

abbrev AxisStrings (D m : ℕ) := Fin D → BitString m

/-- The entry of one equality wire on its endpoint labels. -/
def equalityEntry (k : Type*) [Zero k] [One k] {m : ℕ} (x y : BitString m) : k :=
  if x = y then 1 else 0

/-- The manuscript's tensor `C_{D,m}` in terminal coordinates. -/
def crossingEntry (k : Type*) [CommSemiring k] {D m : ℕ} (_center : Unit)
    (minus plus : AxisStrings D m) : k :=
  ∏ i, equalityEntry k (minus i) (plus i)

theorem crossingEntry_eq_indicator (k : Type*) [CommSemiring k] {D m : ℕ}
    (c : Unit) (minus plus : AxisStrings D m) :
    crossingEntry k c minus plus = if minus = plus then 1 else 0 := by
  simp only [crossingEntry, equalityEntry, Fintype.prod_boole]
  by_cases h : minus = plus
  · simp [h]
  · simp [h, show ¬ ∀ i, minus i = plus i from fun H ↦ h (funext H)]

/-- Each internal wire label is summed once. Both endpoint tables on that
diameter identify this common label with the respective terminal string. -/
def directContraction (k : Type*) [CommSemiring k] {D m : ℕ} (_center : Unit)
    (minus plus : AxisStrings D m) : k :=
  ∑ wire : AxisStrings D m,
    ∏ i, equalityEntry k (minus i) (wire i) * equalityEntry k (wire i) (plus i)

theorem directContraction_eq_crossingEntry (k : Type*) [CommSemiring k] {D m : ℕ}
    (c : Unit) (minus plus : AxisStrings D m) :
    directContraction k c minus plus = crossingEntry k c minus plus := by
  unfold directContraction
  simp_rw [Finset.prod_mul_distrib]
  change (∑ wire, crossingEntry k c minus wire * crossingEntry k c wire plus) = _
  simp_rw [crossingEntry_eq_indicator, ite_mul, one_mul, zero_mul]
  simp

/-- Split each width-`mj` terminal into the strings carried by the `j`
copies of a width-`m` crossing, with a fixed order on the bit coordinates. -/
def stringBlock {D m j : ℕ} (x : AxisStrings D (m * j)) (a : Fin j) : AxisStrings D m :=
  fun i t ↦ x i (finProdFinEquiv (t, a))

/-- Under the bit-coordinate identification, `C_{D,mj} = C_{D,m}^{⊗j}`. -/
theorem crossingEntry_tensorPower (k : Type*) [CommSemiring k] {D m j : ℕ} (c : Unit)
    (minus plus : AxisStrings D (m * j)) :
    crossingEntry k c minus plus =
      ∏ a : Fin j, crossingEntry k c (stringBlock minus a) (stringBlock plus a) := by
  have h : (∀ a : Fin j, stringBlock minus a = stringBlock plus a) ↔ minus = plus := by
    constructor
    · intro hb
      funext i u
      obtain ⟨⟨t, a⟩, rfl⟩ := finProdFinEquiv.surjective u
      exact congrFun (congrFun (hb a) i) t
    · rintro rfl a
      rfl
  simp_rw [crossingEntry_eq_indicator]
  rw [Fintype.prod_boole]
  by_cases he : minus = plus
  · simp [he]
  · simp [he, h]

/-- The widths times the Euclidean lengths of the `D` direct wires, summed
with the actual marked points as their endpoints. -/
noncomputable def directWireCost (D m : ℕ) : ℝ :=
  ∑ i : Fin D, (m : ℝ) * dist (EuclideanSpace.single i (-1 : ℝ)) (EuclideanSpace.single i 1)

theorem directWireCost_eq (D m : ℕ) : directWireCost D m = 2 * D * m := by
  simp [directWireCost, Real.dist_eq]
  ring

end Crossing

end SpectralBooks
end LinearAlgebra
end OAI

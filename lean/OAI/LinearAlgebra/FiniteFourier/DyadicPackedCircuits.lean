import OAI.LinearAlgebra.FiniteFourier.PackedReduction
import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicGridConversion
import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicSectorWords
import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicPackedAssemblyFinal
import OAI.LinearAlgebra.FiniteFourier.DyadicTransformCost

/-! # The denominator-protected dyadic convolution reductions

For each of the two disjoint dyadic prime lists a single encoder acts on both
inputs. Its coefficient ring avoids every excluded denominator, with the same
cost constant for all finite sets of excluded primes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Lemma 7.2 of the predecessor, in the open form used for Theorem 9.3 of the
companion. The estimate requires only the integral unit-shear tensor circuits. -/
theorem dyadicPackedCircuits_of_integralShear {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (ht : IntegralShearBound β C) : ∃ K > 0, DyadicPackedCircuits GaussianRationals β K := by
  classical
  let A := AtTwoCost.wordConstant C β
  have hA : 0 ≤ A := AtTwoCost.wordConstant_nonneg hC
  refine ⟨27*A+27*A+10485, by positivity, ?_⟩
  intro η n B D hn hB L hL
  obtain ⟨T⟩ := exists_dyadicCoefficientTower D L hB (fun l hl => (hL l hl).1)
    (fun l hl => (hL l hl).2.2)
  let := T.domain
  let (p : D.packing.axes) : Fact p.val.Prime := ⟨T.axis_prime p.property⟩
  let r := D.packing.jet
  let e := listCyclotomicDegree GaussianRationals D.pool B
  let cut := D.packing.childCutoff 6
  let H (S : Finset D.packing.axes) := 2*r + S.card
  have hr : 0 < r := by
    have hb : (1:ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
    exact_mod_cast (zero_lt_one.trans_le (hb.trans D.packing.jet_lower))
  have hs (S : Finset D.packing.axes) : 2*e*(H S) ≤ cut := by
    calc
      _ ≤ 2*e*(3*r) := Nat.mul_le_mul_left _ (D.packing.dyadicHeight_le S)
      _ = _ := by change 2*e*(3*r) = 6*e*r; ring
  obtain ⟨pf,pb⟩ := T.primeGrid_circuits hn hβ hC (ht.shearTensorBound _)
  have sectors (S : Finset D.packing.axes) := T.sectorFourierCircuits S
    (fun i => T.axisRoot i.property) (fun i j k hjk => T.axisRoot_separate i.property j k hjk)
    (by dsimp [H]; omega : 0 < H S) (hs S) ht hβ hC
  apply T.protectedList_of_fourierCircuits hn pf pb
    (fun S => (sectors S).1) (fun S => (sectors S).2)
  · apply le_of_eq
    unfold PrimeJetPacking.widthWork
    dsimp only [A]
    ring
  · exact D.packing.dyadic_fourierCosts_le hn hB (fun _ hp => (T.axis_prime hp).two_le)
      (D.packing.childCutoff_pos hn (by decide)) hC hβ

end FiniteFourier
end LinearAlgebra
end OAI

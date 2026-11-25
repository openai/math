import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridAssembly
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoPackedOpen
import OAI.LinearAlgebra.FiniteFourier.PrimeJetPacking.AtTwoPackedAxes
import OAI.LinearAlgebra.FiniteFourier.AtTwoCost.AtTwoPackedTransformCost
import OAI.LinearAlgebra.FiniteFourier.PrimeJetPacking.DyadicPackedAssemblyCost
import OAI.LinearAlgebra.FiniteFourier.PackedReduction

/-! # The packed open convolution at the prime two

Each transformed grid position has a jet of height twice the original height
plus twice the number of prime axes. All three product calls at that position
fit the child length cutoff, and the transform work is charged to the volume
of the original packing.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open ConvolutionGrid Deformation Polynomial
open scoped BigOperators Classical

variable {n B M : ℕ}

/-- The protected prime-axis and jet circuits, followed by CRT packing and
readout, compute ordinary convolution at the cost of the two transforms,
the gather, and the point products. -/
private theorem open_convolution_at_two {σ : Type} [Fintype σ] {p : σ → ℕ}
    [∀ i, Fact (p i).Prime] {hM : Odd M} {hp : ∀ i, p i % 4 = 3} {h7 : ∀ i, 7 ≤ p i}
    {r s : ℕ} {β C : ℝ} (a : ∀ i, AtTwoPrimeAxis M (p i) hM (hp i) (h7 i))
    (width : ∀ i, (p i-1)/2 ≤ B) (h3 : ∀ k, 3^k ≤ 8*B → 3^k ∣ M)
    (hr : 0 < r) (hd : Fintype.card σ ≤ r) (hs : 2*M.totient*(2*r+2*Fintype.card σ) ≤ s)
    (hv : ∏ i, p i ≤ n) (hB : 6 ≤ B) (cop : Pairwise (Function.onFun Nat.Coprime p))
    (cap : 8*n ≤ M.totient*r*(∏ i, p i)) (ht : IntegralShearBound β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    let J := Σ S : Finset σ, ∀ i : S, Fin 2 × Fin ((p i.val-1)/2)
    let H := fun _ : J => 2*r+2*Fintype.card σ
    ∃ u v : ℕ, ((2*u+v : ℕ) : ℝ) ≤ 3*(3*AtTwoCost.wordConstant C β+192)*
        (((∏ i, p i : ℕ) : ℝ)*M.totient*r)*AtTwoCost.rate n r s B β ∧
      ∃ q : OpenConvolution TwoLocalBase n (J × Fin 3) (jetBlockLength (fun _ => M.totient) H),
        q.RealizesMultiple 1 ∧ q.linearCost ≤ 2*u+v+M.totient*r*(∏ i, p i)+
          ∑ b, JetAssembly.blockCost M.totient (H b) := by
  intro J H
  have grid := assembleAtTwoGrid a width h3 hr hd hs hv hB ht hβ hC
  exact exists_openConvolution_of_atTwoGrid p cop hM.pos hr
    (B := J) (H := H) (fun _ => by dsimp [H]; omega) cap grid

/-- The long jet height and the number of sectors give the required child
length, total child volume and linear work in this packing. -/
theorem PrimeJetPacking.protectedList_of_atTwoOpen {n B M : ℕ} {P : Finset ℕ}
    (A : PrimeJetPacking P n M.totient B) (hn : 0 < n) (hB : 6 ≤ B)
    {hM : Odd M} (a : A.AtTwoPackedAxes hM) {β C : ℝ} (hC : 0 ≤ C)
    {u v : ℕ}
    (huv : ((2*u+v:ℕ) : ℝ) ≤ 3*(3*AtTwoCost.wordConstant C β+192)*
      (((∏ i : A.axes, i.val : ℕ) : ℝ)*M.totient*A.jet)*
      AtTwoCost.rate n A.jet (A.childCutoff 8) B β)
    (q : OpenConvolution TwoLocalBase n (A.AtTwoPoint × Fin 3)
      (jetBlockLength (fun _ => M.totient) (fun _ => 2*A.jet+2*Fintype.card A.axes)))
    (hq : q.RealizesMultiple 1)
    (hc : q.linearCost ≤ 2*u+v+M.totient*A.jet*(∏ i : A.axes, i.val) +
      ∑ _ : A.AtTwoPoint, JetAssembly.blockCost M.totient (2*A.jet+2*Fintype.card A.axes)) :
    ProtectedPackedList n {2} (3*8*(9*n)) (A.childCutoff 8)
      (A.widthWork (27*(3*AtTwoCost.wordConstant C β+192)+1305) β (A.childCutoff 8)) := by
  have hB' : (1:ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hh := AtTwoCost.weighted_cost_le_widthWork (β := β) A hn (A.childCutoff_pos hn (by decide : 0 < 8)) hB' hC
  have hprod : (∏ i : A.axes, i.val) = ∏ p ∈ A.axes, p := Finset.prod_coe_sort A.axes id
  rw [hprod] at huv hc
  have hp := A.protectedList_of_jetBlockCost (L := {2}) (C := 27*(3*AtTwoCost.wordConstant C β+192))
    (β := β) (J := A.AtTwoPoint) hn hB' (k := 4) (by decide) (A.card_atTwoPoint a.mod4)
    (fun _ => 2*A.jet+2*Fintype.card A.axes) (fun _ => a.long_height) q hq hc (huv.trans hh)
  convert hp using 2
  norm_num
  ring

private theorem sum_instance_eq {ι : Type*} (a b : Fintype ι) (f : ι → ℕ) :
    Finset.sum (@Finset.univ ι a) f = Finset.sum (@Finset.univ ι b) f := by
  cases Subsingleton.elim a b
  rfl

/-- The unit-shear tensor circuit supplies the two-local list for the
integral convolution descent, with an absolute work multiplier depending
only on the exponent and the shear bound. -/
theorem atTwoPackedCircuits_of_integralShear {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (ht : IntegralShearBound β C) : ∃ K > (0 : ℝ), AtTwoPackedCircuits β K := by
  have hK := AtTwoCost.wordConstant_nonneg (β := β) hC
  refine ⟨27*(3*AtTwoCost.wordConstant C β+192)+1305, by positivity, ?_⟩
  intro n B M P A hn hB hM h3 hp
  let a := A.atTwoPackedAxes hM hp
  let := a.prime
  have hc : 2*M.totient*(2*A.jet+2*Fintype.card A.axes) ≤ A.childCutoff 8 := by
    change _ ≤ 8*M.totient*A.jet
    calc
      _ ≤ 2*M.totient*(4*A.jet) := Nat.mul_le_mul_left _ a.long_height.2
      _ = _ := by ring
  obtain ⟨u, v, huv, q, hq, hcost⟩ := open_convolution_at_two a.axis a.half_le h3 a.jet_pos
    a.count_le hc a.volume_le hB a.coprime a.capacity ht hβ hC
  apply A.protectedList_of_atTwoOpen hn hB a hC huv q hq
  refine hcost.trans (Nat.add_le_add_left (le_of_eq ?_) _)
  exact sum_instance_eq _ _ _

end FiniteFourier
end LinearAlgebra
end OAI

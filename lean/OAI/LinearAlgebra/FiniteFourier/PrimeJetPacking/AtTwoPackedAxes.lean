import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeAxis
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridSectorCircuit
import OAI.LinearAlgebra.FiniteFourier.PackedParameters

/-! # The actual two-local axes of a prime jet packing

The primes in the packing simultaneously specify its CRT address, the
two-orbit transforms, and the total number of split products. All products
use the same long height, including the sector with no active axes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace PrimeJetPacking

open Deformation
open scoped BigOperators Classical

variable {P : Finset ℕ} {n B M : ℕ} (A : PrimeJetPacking P n M.totient B)

/-- One output of the transformed two-local product, identified by its active
prime subset and a quadratic and binomial coordinate on each active axis. -/
abbrev AtTwoPoint := Σ S : Finset A.axes, (i : S) → Fin 2 × Fin ((i.val.val - 1)/2)

theorem card_atTwoPoint (hp : ∀ i : A.axes, i.val % 4 = 3) :
    Fintype.card A.AtTwoPoint = ∏ p ∈ A.axes, p := by
  let K (i : A.axes) := Fin 2 × Fin ((i.val-1)/2)
  let e : A.AtTwoPoint ≃ (∀ i, Option (K i)) := ConvolutionGrid.sectorEquiv (K := K)
  calc
    Fintype.card A.AtTwoPoint = Fintype.card (∀ i, Option (K i)) := Fintype.card_congr e
    _ = ∏ i : A.axes, i.val := by
      convert! ConvolutionGrid.card_atTwoGrid (fun i : A.axes => i.val) hp using 1
      simp only [← Nat.card_eq_fintype_card, K]
    _ = _ := Finset.prod_coe_sort A.axes id

/-- Facts and coefficient data for the selected axes entering the CRT
packing and prime-grid Fourier circuits. -/
structure AtTwoPackedAxes (hM : Odd M) where
  [prime : ∀ i : A.axes, Fact i.val.Prime]
  mod4 : ∀ i : A.axes, i.val % 4 = 3
  seven_le : ∀ i : A.axes, 7 ≤ i.val
  half_le : ∀ i : A.axes, (i.val-1)/2 ≤ B
  axis : ∀ i : A.axes, AtTwoPrimeAxis M i.val hM (mod4 i) (seven_le i)
  coprime : Pairwise (Function.onFun Nat.Coprime (fun i : A.axes => i.val))
  volume_pos : 0 < ∏ i : A.axes, i.val
  volume_le : (∏ i : A.axes, i.val) ≤ n
  capacity : 8*n ≤ M.totient*A.jet*(∏ i : A.axes, i.val)
  jet_pos : 0 < A.jet
  count_le : Fintype.card A.axes ≤ A.jet
  long_height : 0 < 2*A.jet+2*Fintype.card A.axes ∧
    2*A.jet+2*Fintype.card A.axes ≤ 4*A.jet

/-- Instantiate the coefficient-ring prime-axis presentations from the
divisibilities of the half-predecessors, with their sizes in the actual
packing. -/
noncomputable def atTwoPackedAxes (hM : Odd M)
    (h : ∀ p ∈ A.axes, p.Prime ∧ p ≤ B ∧ 7 ≤ p ∧ p % 4 = 3 ∧ (p-1)/2 ∣ M) :
    A.AtTwoPackedAxes hM := by
  letI : ∀ i : A.axes, Fact i.val.Prime := fun i => ⟨(h i.val i.property).1⟩
  let hmod (i : A.axes) := (h i.val i.property).2.2.2.1
  let h7 (i : A.axes) := (h i.val i.property).2.2.1
  have hd : Fintype.card A.axes ≤ A.jet := by
    rw [Fintype.card_coe]
    exact_mod_cast A.axes_le.trans A.jet_lower
  have hB : 7 ≤ B := by
    obtain ⟨p,hp⟩ := A.axes_nonempty
    exact (h7 ⟨p,hp⟩).trans (h p hp).2.1
  have hj : B ≤ A.jet := by exact_mod_cast A.jet_lower
  refine ⟨hmod, h7, fun i => ?_,
    fun i => atTwoPrimeAxis hM (hmod i) (h7 i) (h i.val i.property).2.2.2.2,
    fun i j hij => (Nat.coprime_primes (Fact.out (p := i.val.Prime))
      (Fact.out (p := j.val.Prime))).mpr (fun he => hij (Subtype.ext he)),
    Finset.prod_pos (fun i _ => (h i.val i.property).1.pos), ?_, ?_, by omega, hd, by omega⟩
  · exact (Nat.div_le_self ..).trans ((Nat.sub_le ..).trans (h i.val i.property).2.1)
  · exact (Finset.prod_coe_sort A.axes id).le.trans A.product_le
  · rw [show (∏ i : A.axes, i.val) = ∏ p ∈ A.axes, p from Finset.prod_coe_sort A.axes id]
    simpa only [mul_rotate] using A.volume_lower

end PrimeJetPacking

end FiniteFourier
end LinearAlgebra
end OAI

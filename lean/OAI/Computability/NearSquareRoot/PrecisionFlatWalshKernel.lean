import OAI.Computability.NearSquareRoot.KernelNormalization
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshKernelAddress
import OAI.Computability.NearSquareRoot.PhysicalWalshSemantics
import OAI.Computability.NearSquareRoot.SynchronizedPhysicalFiber

/-! # The exact kernel plan on a packed even-width Walsh piece

A correct recursive kernel plan acts on the paired columns of an active
address. Their slot-major tape serialization gives the same normalized
character on the packed ordinal. Each row of the template keeps its own
input bank throughout the resulting Walsh transform.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshKernel

open Finset Matrix KernelPass SynchronizedPair

noncomputable section

def bitFactor (x y : Bool) : ℂ := (w : ℂ) * (if x && y then -1 else 1)

theorem bitPair (y x : Fin 2 → ZMod 2) :
    (pairEntry y x : ℂ) = ∏ b, bitFactor (decide (y b = 1)) (decide (x b = 1)) := by
  have h (a b c d : ZMod 2) :
      (((if a*c + b*d = 0 then 1/2 else -(1/2)) : ℚ) : ℂ) =
        bitFactor (decide (a = 1)) (decide (c = 1)) *
          bitFactor (decide (b = 1)) (decide (d = 1)) := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp +decide [bitFactor] <;> norm_num <;>
      first | linear_combination KernelNormalization.normalization_pair | linear_combination -KernelNormalization.normalization_pair
  rw [Fin.prod_univ_two]
  exact h (y 0) (y 1) (x 0) (x 1)

theorem fullFlat {n : ℕ} (y x : Fin (2^n)) :
    BoxFin.flatWalsh Finset.univ y x =
      ∏ p : Fin n, bitFactor (y.val.testBit p.val) (x.val.testBit p.val) := by
  classical
  have hs : BoxFin.offBits Finset.univ y x := by intro p hp; simp at hp
  simp only [BoxFin.flatWalsh, Matrix.of_apply, ite_eq_left hs, bitFactor, prod_mul_distrib,
    prod_const, card_univ, Fintype.card_fin, Bool.and_eq_true]
  congr 1
  rw [← prod_filter]
  simp [BoxFin.physicalOverlap]

/-- The dyadic coefficient of one kernel row in the physical order of its
`2*h` bits per lane. -/
theorem packed_entry {a h : ℕ} (y x : Addr (a+1) h) :
    (↑(∏ t, ∏ j, pairEntry (y t j) (x t j)) : ℂ) =
      BoxFin.flatWalsh Finset.univ (KernelScaleLayout.rank y) (KernelScaleLayout.rank x) := by
  classical
  rw [fullFlat, ← (slots a h).prod_comp]
  simp only [Rat.cast_prod, bitPair, Fintype.prod_prod_type, testBit_rank]
  exact Finset.prod_comm

/-- A certified rational kernel plan computes the normalized packed Walsh
matrix at every address of every bank, including the zero-width piece.
Here `rank` and `address` are the two physical serialization maps. -/
theorem packed_plan {U H R : Type} {a W : ℕ} {p : Plan (a+1) W W} (hp : Correct p)
    (width : U → ℕ) (header : U → H) (store : (u : U) → (Addr (a+1) (width u) → ℚ) → R)
    (u : U) (bank : Bank (a+1) (width u) W) (row : Fin W)
    (y : Addr (a+1) (width u)) :
    (((PhysicalWalsh.exactOps width header store).applyPlan p u bank row y : ℚ) : ℂ) =
      (BoxFin.flatWalsh Finset.univ *ᵥ (fun x => (bank row (KernelScaleLayout.address a (width u) x) : ℂ)))
        (KernelScaleLayout.rank y) := by
  classical
  rw [PhysicalWalsh.applyPlan_correct width header store hp]
  simp only [Function.curry, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, target,
    Function.uncurry_apply_pair, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (KernelScaleLayout.addressEquiv a (width u)).symm.sum_comp]
  simp only [Rat.cast_sum, Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro x _
  change _ = BoxFin.flatWalsh _ _ (KernelScaleLayout.rank x) *
    (bank row (KernelScaleLayout.address a (width u) (KernelScaleLayout.rank x)) : ℂ)
  rw [KernelScaleLayout.address_rank, packed_entry]

end
end FlatWalshKernel

end NearSquareRoot
end Computability
end OAI

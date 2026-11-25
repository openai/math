import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridProduct
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGather
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.ZMod.QuotientRing

/-! # Mixed-radix packing on the grid of prime cyclic axes

The cyclic factor in the packing is the additive group algebra of the whole
CRT grid. Its coordinate product is exactly cyclic convolution, and the
integer exponents in the packing basis map to the same residue on every axis.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Module
open scoped BigOperators Classical

noncomputable section

variable {R J G : Type*} [CommRing R] [CommRing J] [Algebra R J] [AddCommMonoid G]
  {e r N n : ℕ}

/-- The two jet power coordinates and the group monomial form the full array basis. -/
def packingBasis (b : Basis (Fin e × Fin r) R J) (E : Fin N ≃ G) :
    Basis (Fin e × Fin r × Fin N) R (AddMonoidAlgebra J G) :=
  (b.smulTower ((AddMonoidAlgebra.basis G J).reindex E.symm)).reindex
    (Equiv.prodAssoc _ _ _)

omit [AddCommMonoid G] in
theorem packingBasis_apply (b : Basis (Fin e × Fin r) R J) (E : Fin N ≃ G)
    (j : Fin e × Fin r × Fin N) :
    packingBasis b E j = AddMonoidAlgebra.single (E j.2.2) (b (j.1,j.2.1)) := by
  simp [packingBasis, Basis.smulTower_apply]

omit [AddCommMonoid G] in
/-- Reading group coefficients directly in the mixed-radix basis. -/
theorem packingBasis_repr (b : Basis (Fin e × Fin r) R J) (E : Fin N ≃ G)
    (v : AddMonoidAlgebra J G) (j : Fin e × Fin r × Fin N) :
    (packingBasis b E).repr v j = b.repr (v.coeff (E j.2.2)) (j.1,j.2.1) := by
  simp [packingBasis, Basis.smulTower_repr, AddMonoidAlgebra.basis]

/-- The product in the grid group algebra agrees with the bilinear cyclic
convolution used in the prime-axis tensor transformation. -/
theorem coeff_mul_cyclicProduct [Fintype G] (x y : AddMonoidAlgebra J G) :
    ⇑(x*y).coeff = cyclicProduct (R := J) x.coeff y.coeff := by
  funext g
  rw [AddMonoidAlgebra.coeff_mul]
  rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
  apply Finset.sum_congr rfl
  intro i _
  exact Finsupp.sum_fintype _ _ (fun j => by simp)

/-- In a CRT cyclic grid, mixed-radix packing followed by group convolution
and gathering computes ordinary convolution. -/
theorem gather_grid_packed (b : Basis (Fin e × Fin r) R J) (u v : J)
    (hb : ∀ i j, b (i,j) = u^i.val * v^j.val) (E : Fin N ≃ G) (g : G)
    (hE : ∀ k : Fin N, E k = k.val • g) (he : 0 < e) (hr : 0 < r)
    (hcap : 8*n ≤ e*r*N) (x y : Fin n → R) (k : Fin (2*n-1)) :
    let B := packingBasis b E
    gatherConvolutionOutput B k.val
      (packConvolutionInput B he hr hcap x * packConvolutionInput B he hr hcap y) =
        openConv R n x y k := by
  apply gather_packed_product _ (AddMonoidAlgebra.single 0 u) (AddMonoidAlgebra.single 0 v)
    (AddMonoidAlgebra.single g 1)
  intro ijk
  rw [packingBasis_apply, hb, hE]
  simp [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]

/-- Number a tuple of residues by the Chinese remainder bijection. -/
def primeResidues {ι : Type*} [Fintype ι] (p : ι → ℕ) [NeZero (∏ i, p i)]
    (cop : Pairwise (Function.onFun Nat.Coprime p)) :
    Fin (∏ i, p i) ≃ (∀ i, ZMod (p i)) :=
  ((ZMod.finEquiv _).trans (ZMod.prodEquivPi p cop)).toEquiv

theorem primeResidues_apply {ι : Type*} [Fintype ι] (p : ι → ℕ) [NeZero (∏ i, p i)]
    (cop : Pairwise (Function.onFun Nat.Coprime p)) (k : Fin (∏ i, p i)) :
    primeResidues p cop k = k.val • (1 : ∀ i, ZMod (p i)) := by
  have hfin (a : ℕ) [NeZero a] (k : Fin a) : ZMod.finEquiv a k = (k.val : ZMod a) := by
    cases a with
    | zero => exact False.elim ((NeZero.ne 0) rfl)
    | succ a => exact (Fin.cast_val_eq_self k).symm
  change ZMod.prodEquivPi p cop (ZMod.finEquiv _ k) = _
  rw [hfin, map_natCast]
  simp [nsmul_eq_mul]

end
end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
import OAI.LinearAlgebra.SpectralBooks.SiteRankFunctional
import OAI.LinearAlgebra.SpectralBooks.WireProduct

/-! # Three-site wire classes as partial diagonals -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

open scoped Classical

private def occupiedLeg {α : Type} {p : Prop} (h : p) : α ≃ (p → α) where
  toFun a _ := a
  invFun f := f h
  left_inv _ := rfl
  right_inv _ := rfl

private def emptyLeg {α : Type} {p : Prop} (h : ¬ p) : Unit ≃ (p → α) where
  toFun _ hp := (h hp).elim
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := funext fun hp ↦ (h hp).elim

private def threeLegs {A : Fin 3 → Type*} (x : A 0) (y : A 1) (z : A 2) : ∀ i, A i :=
  Fin.cons x (Fin.cons y (Fin.cons z (fun i ↦ i.elim0)))

variable (F : Type*) [Field F]

private theorem coeff_pair {I α : Type} [Fintype I] [DecidableEq I] [Fintype α]
    (i j : I) (x : ∀ k, MaskLeg {i, j} α k) :
    (Raw.maskDiagonal F {i, j} α).coeff x =
      if x i (by simp) = x j (by simp) then 1 else 0 := by
  classical
  rw [Raw.maskDiagonal_coeff_at (K := F) {i, j} (Finset.mem_insert_self _ _) x]
  congr 1
  apply propext
  constructor
  · intro h
    exact (h j (by simp)).symm
  · intro h k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · rfl
    · obtain rfl := Finset.mem_singleton.mp hk
      exact h.symm

/-- The first two factors of the curried wire carry its common label. -/
theorem ofRaw_ofThree_wire12 (n : ℕ) :
    ofRaw (ofThree (wire12 F n)) = ofRaw (Raw.maskDiagonal F ({0, 1} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {0, 1}
  let e : ∀ i, (ofThree (wire12 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (occupiedLeg (by decide)) (occupiedLeg (by decide)) (emptyLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair F (0 : Fin 3) 1 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire12]
  split_ifs <;> first | rfl | contradiction

/-- The last two factors of the curried wire carry its common label. -/
theorem ofRaw_ofThree_wire23 (n : ℕ) :
    ofRaw (ofThree (wire23 F n)) = ofRaw (Raw.maskDiagonal F ({1, 2} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {1, 2}
  let e : ∀ i, (ofThree (wire23 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (emptyLeg (by decide)) (occupiedLeg (by decide)) (occupiedLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair F (1 : Fin 3) 2 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire23]
  split_ifs <;> first | rfl | contradiction

/-- The third and first factors of the curried wire carry its common label. -/
theorem ofRaw_ofThree_wire31 (n : ℕ) :
    ofRaw (ofThree (wire31 F n)) = ofRaw (Raw.maskDiagonal F ({2, 0} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {2, 0}
  let e : ∀ i, (ofThree (wire31 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (occupiedLeg (by decide)) (emptyLeg (by decide)) (occupiedLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair F (2 : Fin 3) 0 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire31]
  split_ifs <;> first | rfl | contradiction

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

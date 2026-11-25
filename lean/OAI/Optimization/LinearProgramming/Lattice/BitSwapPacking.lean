import OAI.Optimization.LinearProgramming.Lattice.BitMatrix

/-! Row-major packing commutes with adjacent row swaps and single vector writes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open Hex.Internal

theorem eq_packed_of_rows {n m : ℕ} (rows : IntMatrix) (A : Hex.Matrix ℤ n m)
    (hlen : rows.length=n) (h : ∀ i : Fin n, rowAt rows i.val=packVector (A.getRow i)) :
    rows=packMatrix A := by
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi _
    have hin : i<n := hlen ▸ hi
    have hh := h ⟨i,hin⟩
    change readAt [] rows i = _ at hh
    rw [readAt_eq_getElem [] rows i hi] at hh
    simpa [packMatrix] using hh

theorem swapRows_packMatrix {n m : ℕ} (A : Hex.Matrix ℤ n m) (p k : Fin n) :
    swapRows p.val k.val (packMatrix A) = packMatrix (Hex.Matrix.rowSwap A p k) := by
  apply eq_packed_of_rows _ _ (by simp)
  intro i
  rw [rowAt_swapRows (A := packMatrix A) (i := p.val) (j := k.val) (by simp) (by simp)]
  simp only [rowAt_packMatrix]
  by_cases hip : i=p
  · subst i
    rw [ite_eq_left rfl]
    apply congrArg packVector
    apply Vector.ext
    intro j hj
    let t : Fin m := ⟨j,hj⟩
    change A[k][t] = (Hex.Matrix.rowSwap A p k)[p][t]
    rw [Hex.Matrix.getElem_rowSwap]
    by_cases hpk : p=k <;> simp [hpk]
  · have hp : i.val≠p.val := fun e => hip (Fin.ext e)
    by_cases hik : i=k
    · subst i
      rw [ite_eq_right hp,ite_eq_left rfl]
      apply congrArg packVector
      apply Vector.ext
      intro j hj
      let t : Fin m := ⟨j,hj⟩
      change A[p][t] = (Hex.Matrix.rowSwap A p k)[k][t]
      rw [Hex.Matrix.getElem_rowSwap,ite_eq_left rfl]
    · have hk : i.val≠k.val := fun e => hik (Fin.ext e)
      rw [ite_eq_right hp,ite_eq_right hk]
      apply congrArg packVector
      apply Vector.ext
      intro j hj
      let t : Fin m := ⟨j,hj⟩
      change A[i][t] = (Hex.Matrix.rowSwap A p k)[i][t]
      rw [Hex.Matrix.getElem_rowSwap,ite_eq_right hik,ite_eq_right hip]

theorem packVector_set {α : Type} {n : ℕ} (v : Vector α n) (k : Fin n) (x : α) :
    (packVector v).set k.val x = packVector (v.set k.val x) := by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    have hin : i<n := by simpa using hi
    rw [List.getElem_set]
    simp only [packVector,List.getElem_ofFn]
    change (if k.val=i then x else v[i]) = (v.set k.val x)[i]
    rw [Vector.getElem_set k.isLt hin]


end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

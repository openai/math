import OAI.Optimization.LinearProgramming.Lattice.BitColumn

/-! The binary column transition agrees at every stored basis and coefficient entry
with the actual Hex reduction. The input need not satisfy a Gram validity predicate. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open Hex.Internal

theorem rangeMap_eq_packVector {α : Type} {n : ℕ} (f : ℕ → α) (v : Vector α n)
    (h : ∀ i : Fin n, f i.val = v.get i) :
    (List.range n).map f = packVector v := by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    have hin : i < n := by simpa using hi
    simpa [packVector] using h ⟨i,hin⟩

theorem replace_packed_row {n m : ℕ} (A B : Hex.Matrix ℤ n m) (k : Fin n) (new : List ℤ)
    (hk : new = packVector (B.getRow k))
    (hne : ∀ i : Fin n, i ≠ k → A.getRow i = B.getRow i) :
    (packMatrix A).set k.val new = packMatrix B := by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    have hin : i < n := by simpa using hi
    rw [List.getElem_set]
    by_cases h : k.val = i
    · subst i
      simpa [packMatrix] using hk
    · simpa [packMatrix,h] using congrArg packVector (hne ⟨i,hin⟩ (by
        intro he; exact h (congrArg Fin.val he).symm))

theorem columnPair_packState {n m : ℕ} (s : LLLState n m) (j k : Fin n) :
    columnPair ((j.val,k.val),packState s) =
      ((s.ν.getRow k).get j, s.d.get ⟨j.val+1,Nat.succ_lt_succ j.isLt⟩) := by
  change (entryAt (packMatrix s.ν) k.val j.val,readAt 0 (packVector s.d) (j.val+1)) = _
  rw [entryAt_packMatrix s.ν k j,readAt_packVector 0 s.d ⟨j.val+1,Nat.succ_lt_succ j.isLt⟩]

def nativeColumnNuRow {n m : ℕ} (s : LLLState n m) (j k : Fin n) (r : ℤ) (d : ℕ) : Vector ℤ n :=
  let row := Fin.foldl j.val (fun (row : Vector ℤ n) (l : Fin j.val) =>
    let idx : Fin n := ⟨l.val, lt_trans l.isLt j.isLt⟩
    row.set idx ((s.ν.getRow k).get idx - r*(s.ν.getRow j).get idx)) (s.ν.getRow k)
  row.set j ((s.ν.getRow k).get j - r*(d:ℤ))

theorem nativeColumnNuRow_get {n m : ℕ} (s : LLLState n m) (j k i : Fin n) (r : ℤ) (d : ℕ) :
    (nativeColumnNuRow s j k r d).get i =
      if i.val < j.val then (s.ν.getRow k).get i-r*(s.ν.getRow j).get i
      else if i=j then (s.ν.getRow k).get i-r*(d:ℤ) else (s.ν.getRow k).get i := by
  let row := Fin.foldl j.val (fun (row : Vector ℤ n) (l : Fin j.val) =>
    let idx : Fin n := ⟨l.val, lt_trans l.isLt j.isLt⟩
    row.set idx ((s.ν.getRow k).get idx-r*(s.ν.getRow j).get idx)) (s.ν.getRow k)
  change (row.set j.val _)[i.val] = _
  rw [Vector.getElem_set j.isLt i.isLt]
  by_cases h : j=i
  · subst i; simp
  · have hval : j.val ≠ i.val := fun he => h (Fin.ext he)
    rw [ite_eq_right hval,ite_eq_right (Ne.symm h)]
    exact LLLState.foldl_finRange_set_outerSubMul_get_eq j.val j.isLt.le
      (s.ν.getRow k) (s.ν.getRow k) (s.ν.getRow j) r i

theorem columnNuRow_packState {n m : ℕ} (s : LLLState n m) (j k : Fin n) :
    let z := columnPair ((j.val,k.val),packState s)
    columnNuRow ((j.val,k.val),packState s) =
      packVector (nativeColumnNuRow s j k (nearest z) z.2) := by
  change (List.range (rowAt (packMatrix s.ν) k.val).length).map _ = _
  rw [rowAt_packMatrix, length_packVector]
  apply rangeMap_eq_packVector
  intro i
  rw [nativeColumnNuRow_get]
  simp [columnNuEntry, packState, Fin.ext_iff]

theorem columnBasisMatrix_packState {n m : ℕ} (s : LLLState n m) (j k : Fin n) :
    let x : ColumnArg := ((j.val,k.val),packState s)
    (packMatrix s.b).set k.val (columnBasisRow x) =
      packMatrix (Hex.GramSchmidt.Int.sizeReduce s.b j k (nearest (columnPair x))) := by
  let x : ColumnArg := ((j.val,k.val),packState s)
  let r := nearest (columnPair x)
  apply replace_packed_row
  · change (List.range (rowAt (packMatrix s.b) k.val).length).map _ = _
    rw [rowAt_packMatrix, length_packVector]
    apply rangeMap_eq_packVector
    intro i
    change entryAt (packMatrix s.b) k.val i.val - r*entryAt (packMatrix s.b) j.val i.val =
      (Hex.Matrix.rowAdd s.b j k (-r))[k][i]
    rw [entryAt_packMatrix,entryAt_packMatrix,Hex.Matrix.getElem_rowAdd]
    simp [sub_eq_add_neg]
    rfl
  · intro i hi
    apply Vector.ext
    intro l hl
    let t : Fin m := ⟨l,hl⟩
    change s.b[i][t] = (Hex.Matrix.rowAdd s.b j k (-r))[i][t]
    rw [Hex.Matrix.getElem_rowAdd, ite_eq_right hi]

theorem sizeReduceColumn_packState {n m : ℕ} (s : LLLState n m) (j k : Fin n) (hjk : j.val<k.val) :
    sizeReduceColumn j.val k.val (packState s) = packState (s.sizeReduceColumn j k hjk) := by
  let x : ColumnArg := ((j.val,k.val),packState s)
  let a := (s.ν.getRow k).get j
  let d := s.d.get ⟨j.val+1,Nat.succ_lt_succ j.isLt⟩
  let r := LLLState.nearestQuotient a d
  have hp : columnPair x = (a,d) := columnPair_packState s j k
  have hb := columnBasisMatrix_packState s j k
  have hv : (packMatrix s.ν).set k.val (columnNuRow x) =
      packMatrix (s.ν.setRow k (nativeColumnNuRow s j k r d)) := by
    apply replace_packed_row
    · change columnNuRow x = packVector ((s.ν.setRow k (nativeColumnNuRow s j k r d))[k])
      rw [Hex.Matrix.setRow_get_self]
      have h := columnNuRow_packState s j k
      change columnNuRow x = packVector (nativeColumnNuRow s j k (nearest (columnPair x)) (columnPair x).2) at h
      rwa [hp] at h
    · intro i hi
      exact (Hex.Matrix.setRow_row_ne s.ν k i _ hi).symm
  change (packMatrix s.b).set k.val (columnBasisRow x) =
    packMatrix (Hex.GramSchmidt.Int.sizeReduce s.b j k (nearest (columnPair x))) at hb
  rw [hp] at hb
  by_cases h : 2*a.natAbs > d
  · unfold sizeReduceColumn LLLState.sizeReduceColumn
    change (if needsReduction (columnPair x) then _ else _) = _
    rw [hp,show needsReduction (a,d) = true by simpa [needsReduction] using h]
    rw [dite_eq_left h]
    exact congrArg₂ Prod.mk hb (congrArg (fun v => (v,packVector s.d)) hv)
  · unfold sizeReduceColumn LLLState.sizeReduceColumn
    change (if needsReduction (columnPair x) then _ else _) = _
    rw [hp,show needsReduction (a,d) = false by simpa [needsReduction] using h,dite_eq_right h]
    rfl

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

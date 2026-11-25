import OAI.Optimization.LinearProgramming.NormalSubspace.Geometry
import OAI.Optimization.LinearProgramming.Recovery.PriceMatrices

/-! Populate the two high retained matrix windows from the ordinary row-major tape,
including the empty system and the original register zero. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

open RAM RAM.Callable Geometry Geometry.LabelInput Recovery.PriceLayout

variable {K : Type}
variable {r s : Nat}

theorem GeometryHeader.rawTapes [Zero K] {T : Nat} {m : Memory K} (h : GeometryHeader r s T m)
    (xs : List K) (len : xs.length=r*(r+s)+s*(r+s)) (values : ∀ j, m.data j=xs[j]?.getD 0) :
    RawTapes m 0 0 (r*(r+s)+s*(r+s)+4) xs [r,s,r+s] := by
  refine ⟨h.payload,h.payloadLen.trans len.symm,h.address,h.addressLen,h.capacity,?_,?_⟩
  · intro j hj
    simpa [List.getElem?_eq_getElem hj] using values j
  · intro j hj
    have lt : j<3 := hj
    interval_cases j
    · exact h.row0
    · exact h.row1
    · exact h.columns2

theorem GeometryHeader.afterReturn {T : Nat} {m : Memory K} (h : GeometryHeader r s T m) :
    GeometryHeader r s T (m.putIndex 30 0) :=
  ⟨h.row0,h.row1,h.columns2,h.rank,h.columns,h.primal,h.price,h.free,h.indices,h.dual,h.dualRank,
    h.copyPrimal,h.count,h.dualSource,h.dualTarget,h.dualCount,h.zero,h.payload,h.payloadLen,h.address,
    h.addressLen,h.capacity⟩

private def copyNonempty : Block := .branch (.addrLT 215 224) copyRaw .skip

def placeMatrices : Block := .seq copyNonempty copyDual

private theorem copyNonempty_correct [Field K] [LinearOrder K] [IsStrictOrderedRing K] (m : Memory K) {P : K → Prop} (hm : m.AllData P)
    (dst count : Nat) (hzero : m.index 215=0) (hd : m.index 206=dst) (hc : m.index 224=count)
    (disjoint : count<dst) :
    ∃ t k, k ≤ 7*count+8 ∧ Block.Eval (Memory.AllData P) copyNonempty m k t ∧ Copied m t 0 dst count := by
  by_cases empty : count=0
  · exact ⟨m,1,by omega,.branchFalse (by simp [Cond.test,hzero,hc,empty]) (.skip hm),
      ⟨fun _ hi => False.elim (by omega),fun _ _ _ => rfl,fun _ _ _ _ _ => rfl⟩⟩
  · obtain ⟨t,run,post⟩ := copyRaw_spec P m hm dst count hd hc (by omega) disjoint
    refine ⟨t,1+(7*(count-1)+6)+1,by omega,.branchTrue ?_ run,post⟩
    simp [Cond.test,hzero,hc,Nat.pos_of_ne_zero empty]

private theorem primalWord [Zero K] (D : Matrix (Fin r) (Fin (r+s)) K) (E : Matrix (Fin s) (Fin (r+s)) K)
    (i : Fin r) (j : Fin (r+s)) : (rawWords D E)[i.val*(r+s)+j.val]?.getD 0=D i j := by
  rw [rawWords,List.getElem?_append_left (by simpa using matrixWord_lt i j),matrixWords_get,
    Option.getD_some]

private theorem dualWord [Zero K] (D : Matrix (Fin r) (Fin (r+s)) K) (E : Matrix (Fin s) (Fin (r+s)) K)
    (i : Fin s) (j : Fin (r+s)) : (rawWords D E)[r*(r+s)+(i.val*(r+s)+j.val)]?.getD 0=E i j := by
  rw [rawWords,List.getElem?_append_right (by simp [matrixWords_length]),matrixWords_length,Nat.add_sub_cancel_left,
    matrixWords_get,Option.getD_some]

theorem placeMatrices_correct [Field K] [LinearOrder K] [IsStrictOrderedRing K] (D : Matrix (Fin r) (Fin (r+s)) K) (E : Matrix (Fin s) (Fin (r+s)) K)
    (T : Nat) (m : Memory K) {P : K → Prop} (hm : m.AllData P) (h : GeometryHeader r s T m)
    (values : ∀ j, m.data j=(rawWords D E)[j]?.getD 0) :
    let x := buffers r s (r+s) T
    ∃ t k, k ≤ 14*((r+s)*(r+s))+13 ∧ Block.Eval (Memory.AllData P) placeMatrices m k t ∧ Matrices x D E t := by
  let n := r+s
  let L := r*n+s*n
  let x := buffers r s n T
  have square : L=n*n := (Nat.add_mul r s n).symm
  have gap : L<x.primal := by
    have dual : x.dual=256+n*n+T := rfl
    have de := x.dualEnd
    omega
  obtain ⟨v,k,hk,copy,snap⟩ := copyNonempty_correct m hm x.primal L h.zero h.copyPrimal h.count gap
  have index' (i : Nat) (h8 : i ≠ 8) (h9 : i ≠ 9) (h10 : i ≠ 10) (h11 : i ≠ 11) :=
    snap.indexFrame i h8 h9 h10 h11
  obtain ⟨t,move,last⟩ := copyDual_spec P v copy.safe_end (x.primal+r*n) x.dual (s*n)
    ((index' 225 (by decide) (by decide) (by decide) (by decide)).trans h.dualSource)
    ((index' 200 (by decide) (by decide) (by decide) (by decide)).trans h.dualTarget)
    ((index' 220 (by decide) (by decide) (by decide) (by decide)).trans h.dualCount)
    (by have := x.dualHigh;omega) ((x.dualEnd).trans (Nat.le_add_right _ _))
  have same (i : Nat) (h8 : i ≠ 8) (h9 : i ≠ 9) (h10 : i ≠ 10) (h11 : i ≠ 11) :
      t.index i=m.index i := (last.indexFrame i h8 h9 h10 h11).trans (index' i h8 h9 h10 h11)
  have word (i : Nat) (hi : i<L) : v.data (x.primal+i)=(rawWords D E)[i]?.getD 0 := by
    simpa using (snap.words i hi).trans (values (0+i))
  refine ⟨t,k+(7*(s*n)+5),?_,copy.seq move,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change k+(7*(s*n)+5) ≤ 14*(n*n)+13
    have small : s*n≤L := Nat.le_add_left ..
    omega
  · exact (same 129 (by decide) (by decide) (by decide) (by decide)).trans h.rank
  · exact (same 130 (by decide) (by decide) (by decide) (by decide)).trans h.columns
  · exact (same 131 (by decide) (by decide) (by decide) (by decide)).trans h.primal
  · exact (same 132 (by decide) (by decide) (by decide) (by decide)).trans h.price
  · exact (same 133 (by decide) (by decide) (by decide) (by decide)).trans h.free
  · exact (same 136 (by decide) (by decide) (by decide) (by decide)).trans h.indices
  · exact (same 147 (by decide) (by decide) (by decide) (by decide)).trans h.dual
  · exact (same 148 (by decide) (by decide) (by decide) (by decide)).trans h.dualRank
  · intro i j
    change t.data (x.primal+i.val*n+j.val)=D i j
    have bound : i.val*n+j.val < r*n := matrixWord_lt i j
    have outside : x.dual+s*n ≤ x.primal+(i.val*n+j.val) :=
      x.dualEnd.trans (Nat.le_add_right _ _)
    rw [Nat.add_assoc]
    exact (last.dataFrame _ (by omega) (Or.inr outside)).trans
      ((word _ (bound.trans_le (Nat.le_add_right _ _))).trans (primalWord D E i j))
  · intro i j
    have bound : i.val*n+j.val < s*n := matrixWord_lt i j
    rw [Nat.add_assoc,last.words _ bound,Nat.add_assoc]
    exact (word _ (by dsimp [L];omega)).trans (dualWord D E i j)

end NormalSubspace
end LinearProgramming
end Optimization
end OAI

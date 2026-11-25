import OAI.Optimization.LinearProgramming.Lattice.BitSwapPrefix
import OAI.Optimization.LinearProgramming.Lattice.BitSwap

/-! Pointwise agreement of the serialized swap with every coefficient computed
by the native table mutation, including entries on or above the diagonal. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open Hex.Internal

theorem swapNuEntry_native {n m : ℕ} (s : LLLState n m) (k : Fin n) (hk : 0 < k.val)
    (i j : Fin n) :
    swapNuEntry k.val (packState s) i.val j.val = ((s.swapStep k.val).ν.getRow i).get j := by
  let p := Hex.GramSchmidt.prevRow k hk
  have hp : p.val = k.val-1 := rfl
  have hpk : p.val < k.val := by omega
  have hpk' : p ≠ k := by intro e; exact (ne_of_lt hpk) (congrArg Fin.val e)
  let A := s.ν
  let B := (A.getRow k).get p
  let prev := s.d.get ⟨p.val, Nat.lt_succ_of_lt p.isLt⟩
  let curr := s.d.get ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
  let next := s.d.get ⟨k.val+1,Nat.succ_lt_succ k.isLt⟩
  let g : GramQuad := ((prev,curr),(next,B))
  have hg : gramQuad k.val (packState s) = g := gramQuad_packState s k hk
  let pairs : Vector (ℤ × ℤ) n := Vector.ofFn fun r =>
    if _ : k.val<r.val then ((A.getRow r).get k,(A.getRow r).get p) else (0,0)
  let upd (r : Fin n) (row : Vector ℤ n) :=
    let a := (pairs.get r).1
    let b := (pairs.get r).2
    let left := ((prev:ℤ)*a+B*b)/(curr:ℤ)
    let right := ((next:ℤ)*b-B*a)/(curr:ℤ)
    (row.set p.val left).set k.val right
  let pivot := prefixSwapTable A p k
  have native : ((s.swapStep k.val).ν.getRow i).get j =
      ((Fin.foldl n (fun (M : Hex.Matrix ℤ n n) r =>
        if k.val<r.val then M.modifyRow r.val (upd r) else M) pivot).getRow i).get j := by
    unfold LLLState.swapStep
    rw [dite_eq_left k.isLt, dite_eq_left hk]
    rfl
  rw [native,trailingRows_get]
  have read := prefixSwapTable_get A p k i j hpk'
  have read' : (pivot.getRow i).get j = _ := read
  unfold swapNuEntry
  rw [← hp,hg]
  simp only [packState,entryAt_packMatrix]
  by_cases htr : k.val < i.val
  · have hip : i.val ≠ p.val := by omega
    have hik : i.val ≠ k.val := by omega
    have pairsAt : pairs.get i = ((A.getRow i).get k,(A.getRow i).get p) := by
      change (Vector.ofFn _)[i.val] = _
      rw [Vector.getElem_ofFn,dite_eq_left htr]
    rw [ite_eq_left htr,ite_eq_right hip,ite_eq_right hik,ite_eq_left htr]
    dsimp only [upd]
    rw [pairsAt,read_set_intVec,read_set_intVec,read']
    have hip' : i ≠ p := fun h => hip (congrArg Fin.val h)
    have hik' : i ≠ k := fun h => hik (congrArg Fin.val h)
    simp only [hip',hik',↓reduceIte]
    by_cases hjp : j=p
    · subst j
      simp [hpk',hp,swapPair,g,A]
    · by_cases hjk : j=k
      · subst j; simp [ne_of_gt hpk,swapPair,g,A]
      · simp [hjp,hjk,show j.val≠p.val from fun h => hjp (Fin.ext h),
          show j.val≠k.val from fun h => hjk (Fin.ext h), A]
  · simp only [htr,↓reduceIte]
    rw [read']
    simp only [Fin.ext_iff,A]

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

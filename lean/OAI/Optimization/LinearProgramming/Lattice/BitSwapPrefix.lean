import OAI.Optimization.LinearProgramming.Lattice.BitNativeFold

/-! Readback from the two exchanged coefficient prefixes, including the explicit
pivot write made by the native swap implementation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

def prefixSwapTable {n : ℕ} (A : Hex.Matrix ℤ n n) (p k : Fin n) : Hex.Matrix ℤ n n :=
  let T := (A.modifyRow p.val (fun row => copyPrefix (A.getRow k) row p)).modifyRow k.val
    (fun row => copyPrefix (A.getRow p) row p)
  T.modifyRow k.val fun row => row.set p.val ((A.getRow k).get p)

theorem read_set_intVec {n : ℕ} (v : Vector ℤ n) (p j : Fin n) (x : ℤ) :
    (v.set p.val x).get j = if j=p then x else v.get j := by
  change (v.set p.val x)[j.val] = _
  rw [Vector.getElem_set p.isLt j.isLt]
  by_cases h : j=p
  · subst j; simp
  · simp [h,show p.val ≠ j.val from fun e => h (Fin.ext e.symm)]
    rfl

theorem prefixSwapTable_get {n : ℕ} (A : Hex.Matrix ℤ n n) (p k i j : Fin n) (hpk : p≠k) :
    ((prefixSwapTable A p k).getRow i).get j =
      if i=p then if j.val<p.val then (A.getRow k).get j else (A.getRow i).get j
      else if i=k then if j.val<p.val then (A.getRow p).get j else (A.getRow i).get j
      else (A.getRow i).get j := by
  have hv : p.val ≠ k.val := fun h => hpk (Fin.ext h)
  by_cases hip : i=p
  · subst i
    unfold prefixSwapTable
    rw [Hex.Matrix.getRow_modifyRow_ne _ _ _ p (Ne.symm hv),
      Hex.Matrix.getRow_modifyRow_ne _ _ _ p (Ne.symm hv),Hex.Matrix.getRow_modifyRow_self,
      copyPrefix_get]
    simp
  · by_cases hik : i=k
    · subst i
      unfold prefixSwapTable
      rw [Hex.Matrix.getRow_modifyRow_self,Hex.Matrix.getRow_modifyRow_self,
        Hex.Matrix.getRow_modifyRow_ne _ _ _ k hv,read_set_intVec,copyPrefix_get]
      by_cases hjp : j=p
      · subst j; simp [Ne.symm hpk]
      · simp [hjp, Ne.symm hpk]
    · have hpi : p.val ≠ i.val := fun e => hip (Fin.ext e.symm)
      have hki : k.val ≠ i.val := fun e => hik (Fin.ext e.symm)
      unfold prefixSwapTable
      rw [Hex.Matrix.getRow_modifyRow_ne _ _ _ i hki,
        Hex.Matrix.getRow_modifyRow_ne _ _ _ i hki,Hex.Matrix.getRow_modifyRow_ne _ _ _ i hpi]
      simp [hip,hik]

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI

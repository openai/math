import OAI.Optimization.LinearProgramming.Geometry.UniformTable
import OAI.Optimization.LinearProgramming.Geometry.GramEncoding

/-! Read a rectangular scalar tape through its canonical dense encoding. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open RAM Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

theorem dense_encoded {K : Type} {r c base : ℕ} (v : Memory K) (A : Matrix (Fin r) (Fin c) K)
    (eq : uniformRect r c base v=A) (j : ℕ) (hj : j<(encodedGramInput A).length) :
    v.data (base+j)=(encodedGramInput A)[j] := by
  let q : Fin (r*c) := ⟨j,by simpa using hj⟩
  let ij := finProdFinEquiv.symm q
  have idx : ij.1.val*c+ij.2.val=j := by
    have hv := congrArg Fin.val (finProdFinEquiv.apply_symm_apply q)
    change ij.2.val+c*ij.1.val=j at hv
    simpa only [Nat.mul_comm c,Nat.add_comm ij.2.val] using hv
  have value := congrFun (congrFun eq ij.1) ij.2
  change v.data (base+ij.1.val*c+ij.2.val)=A ij.1 ij.2 at value
  have entry : v.data (base+j) = A ij.1 ij.2 := by
    simpa only [Nat.add_assoc,idx] using value
  have lookup : (encodedGramInput A)[j] = A ij.1 ij.2 :=
    List.getElem_ofFn (f := fun z : Fin (r*c) =>
      A (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) hj
  exact entry.trans lookup.symm

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI

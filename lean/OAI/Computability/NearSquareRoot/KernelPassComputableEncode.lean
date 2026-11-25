import OAI.Computability.NearSquareRoot.KernelPassComputablePacked

/-! # Completeness of the numerical template enumeration -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax.Packed

open KernelComputableDyadic KernelComputableSelector

variable {A i o : ℕ}

def mixValues (f : Fin o → Fin i → Coefficient) : List Code :=
  List.ofFn fun j : Fin (o*i) => ofCoefficient
    (f (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

theorem mixValues_get (f : Fin o → Fin i → Coefficient) (b : Fin o) (a : Fin i) :
    coefficient ((mixValues f).getD (b.val*i+a.val) zero) = f b a := by
  have hidx : b.val*i+a.val = (finProdFinEquiv (b,a)).val := by
    change _ = a.val + i*b.val
    ac_rfl
  have hb : (finProdFinEquiv (b,a)).val < (mixValues f).length := by
    rw [mixValues, List.length_ofFn]
    exact (finProdFinEquiv (b,a)).isLt
  rw [hidx, List.getD_eq_getElem _ _ hb]
  simp only [mixValues, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply, coefficient_ofCoefficient]

/-- The code is a finite prefix list, with all tables serialized literally. -/
def encode {A i o : ℕ} : Plan A i o → List Op
  | @Plan.mix _ i o t => [(0,[i,o],mixValues t)]
  | .xor (a,b) => [(1,[a.val,b.val],[])]
  | .scale q f t => [(2,q :: encodeTests f,encodeTable t)]
  | .child a => [(3,[a.val],[])]
  | .seq p q => (4,[],[]) :: encode p ++ encode q
  | .parallel p q => (5,[],[]) :: encode p ++ encode q

private theorem fold_encode {A i o : ℕ} (p : Plan A i o) (s : List (Packed A)) :
    (encode p).foldr (algebra A).step s = (mk i o p) :: s := by
  induction p generalizing s with
  | @mix i o f =>
    change mk i o (.mix fun b a => coefficient ((mixValues f).getD (b.val*i+a.val) zero)) :: s = _
    rw [funext fun b => funext (mixValues_get f b)]
  | xor g =>
    obtain ⟨a,b⟩ := g
    simp [encode, Algebra.step, algebra, leaf, arg, a.isLt, b.isLt]
  | scale q f t =>
    change mk 1 1 (.scale q (test A q (encodeTests f)) (table (encodeTable t))) :: s = _
    rw [test_encode, table_encode]
  | child a =>
    simp [encode, Algebra.step, algebra, leaf, arg, a.isLt]
  | seq p q ihp ihq =>
    simp only [encode, List.foldr_append, List.foldr_cons]
    rw [ihq, ihp]
    change seq (mk _ _ p) (mk _ _ q) :: s = _
    simp [seq]
  | parallel p q ihp ihq =>
    simp only [encode, List.foldr_append, List.foldr_cons]
    rw [ihq, ihp]
    rfl

theorem decode_encode (p : Plan A i o) : decode A (encode p) = mk i o p := by
  simp [decode, Algebra.parse, fold_encode]

end KernelPass.ComputableSyntax.Packed

end NearSquareRoot
end Computability
end OAI

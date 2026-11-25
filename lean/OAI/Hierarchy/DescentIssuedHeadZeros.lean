import OAI.Hierarchy.DescentPublicOperandDisjoint

namespace OAI
/-! A new private lane or surface request describes a cable with a zero correction to its kind and peer. -/
namespace Hierarchy
open DescentSIMDLookup
noncomputable section
namespace DescentRotorOperandQueryROM.Shape

theorem flat_head_zero {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : Shape)
    (mult grain split node arg : ℕ) (x : Fin 4→Cell C.fieldBits) (f : Fin 7) (early : f.val<2) :
    C.flatReg board mult grain split node arg f.succ x=0:=by
  have zero (l : PrivateLane board) (levels within : ℕ) : l.kept board C mult levels grain split within f=0:=by
    fin_cases f <;> first | rfl | norm_num at early
  unfold flatReg
  repeat' first | rfl | exact zero _ _ _ | split | (dsimp only; split)
end DescentRotorOperandQueryROM.Shape

namespace DescentResetPublicOperandBook.Config
theorem public_head_zero {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : Config)
    (bits : ℕ) (j : Fin C.oldConfig.mouths) (x : C.Data n) (f : Fin 7) (early : f.val<2) :
    C.column board bits (some f) j x=0:=by
  let pos : Fin C.args × Fin C.nodes := finProdFinEquiv.symm j
  cases hit : C.mixed board pos.2.val pos.1.val x with
  | none => simp only [column, ←show pos = finProdFinEquiv.symm j from rfl, hit]
  | some out =>
    rcases out with ⟨q, word, count, mark⟩
    simp only [column, ←show pos = finProdFinEquiv.symm j from rfl, hit]
    fin_cases f <;> first | rfl | norm_num at early
end DescentResetPublicOperandBook.Config
end
end Hierarchy

end OAI

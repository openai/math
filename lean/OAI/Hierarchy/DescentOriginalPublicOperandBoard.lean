import OAI.Hierarchy.DescentResetPublicOperandBook

namespace OAI
/-! # Identifying a physically read row after identifying the original board and operand menu -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentPackedZip
noncomputable section
variable {n₀ n₁ d₀ d₁ : ℕ} {A B : Config}
  {left : NonlinearExpanders.Graph n₀ d₀} {right : NonlinearExpanders.Graph n₁ d₁}

def relabel (shape : A=B) (dim : n₀=n₁) (row : A.Data n₀) : B.Data n₁ :=
  shape ▸ dim ▸ row

theorem mixed_relabel (shape : A=B) (dim : n₀=n₁) (degree : d₀=d₁) (board : HEq left right)
    (row : A.Data n₀) (arg node : ℕ) :
    B.mixed right node arg (relabel shape dim row)=A.mixed left node arg row :=by
  subst B
  subst n₁
  subst d₁
  cases eq_of_heq board
  rfl

theorem column_relabel (shape : A=B) (dim : n₀=n₁) (degree : d₀=d₁) (board : HEq left right)
    (row : A.Data n₀) (arg : Fin A.args) (node : Fin A.nodes) (width : ℕ) (field : Option (Fin 7)) :
    B.column right width field
      (finProdFinEquiv (arg.cast (congrArg (fun a:Config=>a.args) shape),node.cast (congrArg (fun a:Config=>a.nodes) shape)))
      (relabel shape dim row)=A.column left width field (finProdFinEquiv (arg,node)) row :=by
  subst B
  subst n₁
  subst d₁
  cases eq_of_heq board
  rfl

theorem flat_relabel (shape : A=B) (dim : n₀=n₁) (degree : d₀=d₁) (board : HEq left right)
    (row : A.Data n₀) (arg node : ℕ) (f : Fin 8) :
    B.rotor.flatReg right B.multiplicity B.grain B.split node arg f (B.reg (relabel shape dim row))=
      A.rotor.flatReg left A.multiplicity A.grain A.split node arg f (A.reg row) :=by
  subst B
  subst n₁
  subst d₁
  cases eq_of_heq board
  rfl

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI

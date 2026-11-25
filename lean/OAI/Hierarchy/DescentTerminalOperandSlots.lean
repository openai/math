import OAI.Hierarchy.DescentTerminalBirthOrdinal
import OAI.Hierarchy.DescentLocalPrivateNames

namespace OAI
/-! # Rectangular addresses of occupied operands in the terminal RAM -/
namespace Hierarchy.DescentTerminalPointerIssue
open DescentKernelHistory DescentLocalPrivateNames DescentTerminalChronologicalBooks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {Tag B : Type} {N A : ℕ} (r:Recipe Tag B) (birth:r.Node↪ℕ)
    (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤A)

def row (u:r.Node) : Fin N := (ordinal birth u).castLE nodes
local notation "nr" => row r birth nodes

/-- The sparse site record is a bounded rectangle with numeric coordinates
(dense chronological node number, true index within that node's operand list). -/
def slot : Slot r↪Fin (N*A) where
  toFun s:=finProdFinEquiv (nr s.1,s.2.castLE (arity s.1))
  inj' := by
    rintro ⟨u,j⟩ ⟨v,k⟩ eqn
    have parts:=finProdFinEquiv.injective eqn
    have hval : (nr u).val=(nr v).val:=congrArg (fun z:Fin N × Fin A=>z.1.val) parts
    have hu:u=v:=(ordinal birth).injective (Fin.ext hval)
    subst v
    have aval : j.val=k.val:=congrArg (fun z:Fin N × Fin A=>z.2.val) parts
    have hj:j=k:=Fin.ext aval
    subst k
    rfl

end
end Hierarchy.DescentTerminalPointerIssue

end OAI

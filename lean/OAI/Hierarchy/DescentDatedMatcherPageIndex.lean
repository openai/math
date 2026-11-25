import OAI.Hierarchy.DescentDatedOperandPages

namespace OAI
/-! The matcher page is indexed by path, block, old outgoing ordinal, and a three-way mode. -/
namespace Hierarchy.DescentDatedOperandPages
open DescentRawCablePanel.DepotRAM
noncomputable section

def matcherIndex (f : Shape) (paths : ℕ) (i : Fin (paths*(f.blocks*(f.cap*3)))) (col : Fin 5) :
    Fin paths × Fin (count f) :=
  let (p,t):=finProdFinEquiv.symm i
  let (x,slot):=finProdFinEquiv.symm t
  let (old,mode):=finProdFinEquiv.symm slot
  (p,if live : mode.val<2 then anchor f x old ⟨mode.val,live⟩ col else sibling f x old col)

end
end Hierarchy.DescentDatedOperandPages

end OAI

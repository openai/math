import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildLiteral
import OAI.Computability.NearSquareRoot.PhysicalWalshChildAdapter

/-! # Contract of the two concrete recursive row frames -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileChild

open IntegerMultiplication Code PhysicalWalshNode

abbrev Stream := List Dusk.Pair

def Adapter (d : ℕ) (down : Control → Cmd) (up : Cmd) : Prop :=
  ∀ (a W : ℕ) (axis : Fin (a+1)), ∃ C : ℕ, ∀ (s : Shape), 0 < s.level → ∀ row : Stream,
    let t := (⟨a,W,axis,s⟩ : World)
    let parent := ChildAdapter.saved a W s
    let h := C*((Header.scale (a+1) s+1)^d + ChildAdapter.volume (a+1) s + size row +1)
    let q := send (parent,[row])
    let dst := Tree.fork (.fork (.atom (tag t).1) (send ((tag t).2,row))) (send parent)
    let reply := Tree.fork (send ((tag t).2,row)) (send parent)
    (∀ env park, Fits env (down (a+1,W,axis.val)) (pile 0 q park) (pile 0 dst park) h) ∧
    (∀ env park, Fits env up (pile 0 reply park) (pile 0 q park) h) ∧
    q.count ≤ h ∧ reply.count ≤ h ∧ size parent ≤ h

end PhysicalWalshCompileChild

end NearSquareRoot
end Computability
end OAI

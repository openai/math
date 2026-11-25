import OAI.Hierarchy.DescentBitDescription
import OAI.Hierarchy.DescentBitHistoryTerminal

namespace OAI
/-! # Equivalence of local and global interfaces for bit-addressed node histories -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F U P : Type} [Field F] {D : ℕ} {w : P→ℕ} (N : Network D P w)
def localBit {v : N.Site} (edge : ∀e : Incident N v,Word (N.width e.val)) (pin : ∀p : Attached N v,Word (w p.val)) :
    BitRef (boundaryWidth N v)→Bool
  | ⟨.inl e,j⟩=>edge e j
  | ⟨.inr p,j⟩=>pin p j

def ReadsLocal (scalar : U→List (List Bool)→F) (r : SiteBits (U:=U) N) (T : N.Tables F) :=
  ∀v e p,(r v).value scalar (localBit N e p)=T v e p

theorem reads_iff_local (scalar : U→List (List Bool)→F) (r : SiteBits (U:=U) N) (T : N.Tables F) :
    ReadsBits N scalar r T ↔ ReadsLocal N scalar r T := by
  constructor
  · intro valid v e p
    let a : N.Assignment := fun edge=>if h : N.src edge=v ∨ N.dst edge=v then e ⟨edge,h⟩ else fun _=>false
    let x : Ports w := fun q=>if h : N.attach q=v then p ⟨q,h⟩ else fun _=>false
    have ea (t : Incident N v) : a t.val=e t := dite_eq_left t.property
    have px (t : Attached N v) : x t.val=p t := dite_eq_left t.property
    have equal : bitInput N a x v=localBit N e p := by
      funext t
      rcases t with ⟨i|i,j⟩
      · exact congrFun (ea i) j
      · exact congrFun (px i) j
    simpa only [equal,Network.read,ea,px] using valid a x v
  · intro valid a x v
    have equal : bitInput N a x v=localBit N (fun e=>a e.val) (fun p=>x p.val) := by
      funext i;rcases i with ⟨_|_,j⟩ <;> rfl
    rw [equal]
    exact valid v _ _

theorem terminal_local (scalar : U→List (List Bool)→F) (r : SiteBits (U:=U) N) (T : N.Tables F)
    (valid : ReadsBits N scalar r T) :
    Represents N (BitRecipe.gatheredScalar scalar) T (fun v=>(r v).asRecipe) := by
  intro v read pins
  let wds : ∀b : Boundary N v,Word (boundaryWidth N v b) := fun b=>match b with
    | .inl e=>read e
    | .inr p=>pins p
  have equal : input N read pins=(fun b=>wordList (wds b)) := by funext b;cases b <;> rfl
  rw [equal,BitRecipe.asRecipe_value]
  have eqBit : (fun i : BitRef (boundaryWidth N v)=>wds i.1 i.2)=localBit N read pins := by
    funext i;rcases i with ⟨_|_,j⟩ <;> rfl
  rw [eqBit]
  exact (reads_iff_local N scalar r T).mp valid v read pins

end
end Hierarchy.DescentKernelHistory

end OAI

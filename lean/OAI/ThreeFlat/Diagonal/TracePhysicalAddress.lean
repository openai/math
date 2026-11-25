import OAI.ThreeFlat.BitNetwork
import OAI.ThreeFlat.Diagonal.TraceSlotFormat
import OAI.ThreeFlat.Diagonal.TraceSharedOrdinal

namespace OAI
/-! # Physical row ports and shared-bit ownership indices -/

namespace ThreeFlat.Diagonal.TracePhysical

open Computability.VPVNP RAMSerialization TraceSlots
variable {w r f S d : ℕ}

/-- CPU slots in a physical row and the next row's first slot cover both
adjacent CPU pairs. Each sort partner is determined by its layer alone.
Header operands read the two inputs owned by this row. -/
abbrev Port (w r d : ℕ) :=
  (Fin 3 × Fin ((5+r)*(w+1))) ⊕
    ((Fin 2 × Fin w) ⊕
      ((Fin (RAMLayout.layerCount d) × Bool × Fin 2 × Fin (7*(w+1))) ⊕
       (Bool × Fin (7*(w+1)))))

abbrev Source (w r f S d : ℕ) := BitSource (Fintype.card (Shared w r f d)) (S*w)

def shared (i : Shared w r f d) : Source w r f S d :=
  .hidden (sharedOrdinal w r f d i)

/-- Read the shared bit, the public header bit, or the canonical constant
for a missing edge. Boundary padding of a sorting record has its one
distinguished padding flag. -/
def address (hw : 2 ≤ w+1) (S f : ℕ) (v : Fin (2^d)) :
    Port w r d → Source w r f S d
  | .inl (c,j) =>
    let a := 2*v.val+c.val
    if S ≤ a then if h : a-S < f then shared (.inl (⟨a-S,h⟩,j)) else .constant false else .constant false
  | .inr (.inl (s,k)) =>
    let a := 2*v.val+s.val
    if h : a < S then .pin (finProdFinEquiv (⟨a,h⟩,k)) else .constant false
  | .inr (.inr (.inl (l,own,s,j))) =>
    shared (.inr (.inl (l,if own then v else ((RAMLayout.layerEquiv d).symm l).partner v,s,j)))
  | .inr (.inr (.inr (out,j))) =>
    if out then
      if h : v.val+1 < 2^d then shared (.inr (.inr (⟨v.val,by omega⟩,j)))
      else .constant ((slotFormat hw).encode none j)
    else if h : 0 < v.val then shared (.inr (.inr (⟨v.val-1,by have := v.isLt; omega⟩,j)))
         else .constant ((slotFormat hw).encode none j)

end ThreeFlat.Diagonal.TracePhysical

end OAI

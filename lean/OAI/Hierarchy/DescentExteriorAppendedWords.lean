import OAI.Computability.VPVNP.RAMMemory
import OAI.ThreeFlat.Diagonal.TraceBanks
import OAI.ThreeFlat.Diagonal.TraceWordTests

namespace OAI
/-! # RAM input words and their Boolean pins on two consecutive ranges -/
namespace Hierarchy.DescentExteriorShelf.Root
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.Diagonal
open Computability.VPVNP.RAMMemory (initialMemory)
noncomputable section
variable {w : ℕ}

def appended (frontSize extra : ℕ) (front back : Memory w) : Memory w :=
  initialMemory (frontSize+extra) (fun a=>if a<frontSize then front a else back (a-frontSize))

theorem append_low (frontSize extra : ℕ) (front back : Memory w) {a : ℕ} (ha : a<frontSize) :
    appended frontSize extra front back a=front a := by
  simp [appended,initialMemory,ha,show a<frontSize+extra by omega]

theorem suffix_read (frontSize extra : ℕ) (front back : Memory w) (i : Fin extra) :
    appended frontSize extra front back (frontSize+i.val)=back i.val := by
  have h:=i.isLt
  simp [appended,initialMemory,show frontSize+i.val<frontSize+extra by omega]

def appendPin {A : Type} (frontSize extra : ℕ)
    (front : Fin frontSize×Fin (w+1)→A⊕Bool) (back : Fin extra×Fin (w+1)→A⊕Bool)
    (i : Fin (frontSize+extra)×Fin (w+1)) : A⊕Bool :=
  if h:i.1.val<frontSize then front (⟨i.1.val,h⟩,i.2)
  else back (⟨i.1.val-frontSize,by have:=i.1.isLt;omega⟩,i.2)

theorem appendPin_read {A : Type} (frontSize extra : ℕ) (x : A→Bool) (first last : Memory w)
    (front : Fin frontSize×Fin (w+1)→A⊕Bool) (back : Fin extra×Fin (w+1)→A⊕Bool)
    (left : ∀i,(front i).elim x id=TraceWords.bits (TraceBanks.wide (first i.1.val)) i.2)
    (right : ∀i,(back i).elim x id=TraceWords.bits (TraceBanks.wide (last i.1.val)) i.2)
    (i : Fin (frontSize+extra)×Fin (w+1)) :
    (appendPin frontSize extra front back i).elim x id=
      TraceWords.bits (TraceBanks.wide (appended frontSize extra first last i.1.val)) i.2 := by
  by_cases small : i.1.val<frontSize
  · rw [appendPin,dite_eq_left small,append_low _ _ _ _ small]
    apply left
  · let rel : Fin extra:=⟨i.1.val-frontSize,by have:=i.1.isLt;omega⟩
    have h : i.1.val=frontSize+rel.val:=by dsimp [rel];omega
    change (appendPin frontSize extra front back i).elim x id=_
    rw [appendPin,dite_eq_right small]
    exact (right (rel,i.2)).trans (congrArg (fun b=>TraceWords.bits (TraceBanks.wide b) i.2)
      ((suffix_read frontSize extra first last rel).symm.trans (congrArg (appended frontSize extra first last) h.symm)))

end
end Hierarchy.DescentExteriorShelf.Root

end OAI

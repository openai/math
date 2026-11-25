import OAI.ThreeFlat.BitNetwork.OrderedPair
import OAI.ThreeFlat.BitNetwork.PinMap
import OAI.ThreeFlat.BitNetwork.RectangularHidden

namespace OAI
/-! # Row-major emission for a hidden-free prefix and a rectangular bucket -/

namespace ThreeFlat.Diagonal.TraceBucketJoin
open scoped BigOperators Classical

variable {F : Type*} [CommSemiring F] {p a b H : ℕ}

def mount {n t m q : ℕ} (wire : Fin t → Fin q) (h : Fin n → Fin m) : BitSource n t → BitSource m q
  | .constant v => .constant v
  | .hidden i => .hidden (h i)
  | .pin j => .pin (wire j)

theorem mount_read {n t m q : ℕ} (wire : Fin t → Fin q) (h : Fin n → Fin m)
    (g : Fin m → Bool) (x : Fin q → Bool) (s : BitSource n t) :
    (mount wire h s).read g x = s.read (g ∘ h) (x ∘ wire) := by cases s <;> rfl

def network (A : BitNetwork F a) (hA : A.internal=0) (B : BitNetwork F b)
    (R : BitNetwork.Rectangular.Address B.internal H) (left : Fin a → Fin p) (right : Fin b → Fin p) :
    BitNetwork F p where
  internal := H
  cells := A.cells+(B.cells+H)
  source := Fin.append (fun i j => mount left (fun h => Fin.elim0 (h.cast hA)) (A.source i j))
    (fun i j => mount right id ((BitNetwork.Rectangular.network B R).source i j))
  table := Fin.append A.table (BitNetwork.Rectangular.network B R).table

theorem eval (A : BitNetwork F a) (hA : A.internal=0) (B : BitNetwork F b)
    (R : BitNetwork.Rectangular.Address B.internal H) (left : Fin a → Fin p) (right : Fin b → Fin p)
    (pin : Fin p → Bool) : (network A hA B R left right).eval pin =
      A.eval (pin ∘ left) * B.eval (pin ∘ right) := by
  classical
  let z : Fin A.internal → Bool := fun h => Fin.elim0 (h.cast hA)
  have lone : A.eval (pin ∘ left)=A.weight (pin ∘ left) z := by
    unfold BitNetwork.eval
    apply Finset.sum_eq_single z
    · intro i _ ne
      exact False.elim (ne (funext (fun h => Fin.elim0 (h.cast hA))))
    · simp
  rw [lone,←BitNetwork.Rectangular.eval B R (pin ∘ right)]
  change (∑ g : Fin H → Bool, ∏ i : Fin (A.cells+(B.cells+H)),
    (network A hA B R left right).factor pin g i) = _*∑ g : Fin H → Bool,_
  refine Eq.trans ?_ (Finset.mul_sum ..).symm
  apply Finset.sum_congr rfl
  intro g _
  have same : g ∘ (fun h : Fin A.internal => (Fin.elim0 (h.cast hA) : Fin H)) = z := by
    funext h
    exact Fin.elim0 (h.cast hA)
  refine (Fin.prod_univ_add (fun i : Fin (A.cells+(B.cells+H)) =>
    (network A hA B R left right).factor pin g i)).trans ?_
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i _
    simp only [network,BitNetwork.factor,Fin.append_left,mount_read,same]
    exact congrFun (Fin.append_left A.table (BitNetwork.Rectangular.network B R).table i) _
  · apply Finset.prod_congr rfl
    intro i _
    simp only [network,BitNetwork.factor,Fin.append_right]
    refine (congrFun (Fin.append_right A.table (BitNetwork.Rectangular.network B R).table i) _).trans ?_
    apply congrArg ((BitNetwork.Rectangular.network B R).table i)
    funext j
    exact mount_read right id g pin ((BitNetwork.Rectangular.network B R).source i j)

end ThreeFlat.Diagonal.TraceBucketJoin

end OAI

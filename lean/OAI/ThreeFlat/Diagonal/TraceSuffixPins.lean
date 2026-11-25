import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Keep paired endpoint pins and specialize the public header suffix -/

namespace ThreeFlat.Diagonal.TraceSuffix
open RAM.BitLayout
variable {F : Type*} {old free ports n : ℕ}

/-- In each bucket the old pins consist of a contiguous external slice followed by both port banks. -/
def source (_clip : free≤old) (start : ℕ) (pub : ℕ→Bool) :
    BitSource n (old+ports) → BitSource n (free+ports)
  | .constant b => .constant b
  | .hidden h => .hidden h
  | .pin j =>
    if h : j.val<free then .pin ⟨j.val,by omega⟩
    else if ho : j.val<old then .constant (pub (start+j.val))
    else .pin ⟨free+(j.val-old),by have := j.isLt; omega⟩

def network (N : BitNetwork F (old+ports)) (clip : free≤old) (start : ℕ) (pub : ℕ→Bool) :
    BitNetwork F (free+ports) where
  internal := N.internal
  cells := N.cells
  source i j := source clip start pub (N.source i j)
  table := N.table

def fullPin (_clip : free≤old) (start : ℕ) (pub : ℕ→Bool) (pin : Fin (free+ports)→Bool)
    (j : Fin (old+ports)) :=
  if h : j.val<free then pin ⟨j.val,by omega⟩
  else if ho : j.val<old then pub (start+j.val)
  else pin ⟨free+(j.val-old),by have := j.isLt; omega⟩

theorem source_read (clip : free≤old) (start : ℕ) (pub : ℕ→Bool) (pin : Fin (free+ports)→Bool)
    (hidden : Fin n→Bool) (s : BitSource n (old+ports)) :
    (source clip start pub s).read hidden pin=s.read hidden (fullPin clip start pub pin) := by
  cases s with
  | constant b => rfl
  | hidden i => rfl
  | pin i =>
    by_cases h : i.val<free <;> by_cases t : i.val<old <;>
      simp [source,BitSource.read,fullPin,h,t]

theorem eval [CommSemiring F] (N : BitNetwork F (old+ports)) (clip : free≤old) (start : ℕ)
    (pub : ℕ→Bool) (pin : Fin (free+ports)→Bool) :
    (network N clip start pub).eval pin=N.eval (fullPin clip start pub pin) := by
  unfold BitNetwork.eval BitNetwork.weight
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (N.table i)
  funext z
  exact source_read clip start pub pin h (N.source i z)

/-- Original trivalent source words use 0/1 for literals, then pins, then private bits. -/
def address (old free start : ℕ) (pub : ℕ→Bool) (x : ℕ) : ℕ :=
  if x<2+free then x else if x<2+old then (pub (start+(x-2))).toNat else x-(old-free)

theorem source_address (clip : free≤old) (start : ℕ) (pub : ℕ→Bool) (s : BitSource n (old+ports)) :
    sourceAddress (source clip start pub s)=address old free start pub (sourceAddress s) := by
  cases s with
  | constant b =>
    have small : b.toNat<2+free:=by cases b <;> simp <;> omega
    change b.toNat=address old free start pub b.toNat
    simp only [address,ite_eq_left small]
  | hidden i =>
    change 2+(free+ports)+i.val=address old free start pub (2+(old+ports)+i.val)
    have outside₀ : ¬2+(old+ports)+i.val<2+free:=by omega
    have outside₁ : ¬2+(old+ports)+i.val<2+old:=by omega
    rw [address,ite_eq_right outside₀,ite_eq_right outside₁]
    omega
  | pin i =>
    by_cases h : i.val<free <;> by_cases t : i.val<old <;>
      simp [source,sourceAddress,address,h,t]; omega

def field (old free start : ℕ) (pub : ℕ→Bool) (j x : ℕ) :=
  if j<3 then address old free start pub x else x

end ThreeFlat.Diagonal.TraceSuffix

end OAI

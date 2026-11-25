import Mathlib.Data.Fin.Tuple.Sort

namespace OAI
/-! # Stability of sorting a tuple after appending a constant greatest record -/

namespace Hierarchy.Tagged.TerminalSort

open scoped Classical
noncomputable section
variable {a b : ℕ} {α κ : Type*} [LinearOrder κ]

def pad (top : α) (x : Fin a→α) (i : Fin b) := if hi : i.val<a then x ⟨i.val,hi⟩ else top

private def push (h : a≤b) (e : Equiv.Perm (Fin a)) (i : Fin b) : Fin b :=
  if hi : i.val<a then Fin.castLE h (e ⟨i.val,hi⟩) else i

private theorem push_inside (h : a≤b) (e : Equiv.Perm (Fin a)) (i : Fin a) :
    push h e (Fin.castLE h i)=Fin.castLE h (e i) := by simp [push,i.isLt]

private theorem push_pair (h : a≤b) (e : Equiv.Perm (Fin a)) (i : Fin b) :
    push h e.symm (push h e i)=i := by
  by_cases hi : i.val<a
  · let j : Fin a:=⟨i.val,hi⟩
    change push h e.symm (push h e (Fin.castLE h j))=Fin.castLE h j
    simp [push_inside]
  · simp [push,hi]

private def liftPerm (h : a≤b) (e : Equiv.Perm (Fin a)) : Equiv.Perm (Fin b) where
  toFun:=push h e
  invFun:=push h e.symm
  left_inv:=push_pair h e
  right_inv:=push_pair h e.symm

theorem sort_pad (h : a≤b) (top : α) (key : α→κ) (greatest : ∀x,key x≤key top)
    (x : Fin a→α) :
    (pad top x : Fin b→α) ∘ Tuple.sort (key ∘ pad top x)=pad top (x ∘ Tuple.sort (key ∘ x)) := by
  let e:=Tuple.sort (key ∘ x)
  have stable := Tuple.eq_sort_iff.mp (rfl : e=Tuple.sort (key ∘ x))
  have inKey (i : Fin a) : key (pad top x (liftPerm h e (Fin.castLE h i)))=key (x (e i)) := by
    change key (pad top x (push h e (Fin.castLE h i)))=_
    simp [push_inside,pad,(e i).isLt]
  have outKey (i : Fin b) (hi : ¬i.val<a) : key (pad top x (liftPerm h e i))=key top := by
    change key (pad top x (push h e i))=_
    simp [push,pad,hi]
  have shape : liftPerm h e=Tuple.sort (key ∘ (pad top x : Fin b→α)) := by
    apply Tuple.eq_sort_iff.mpr
    constructor
    · intro i j hij
      change key (pad top x (liftPerm h e i))≤key (pad top x (liftPerm h e j))
      by_cases hj : j.val<a
      · have hi : i.val < a := Nat.lt_of_le_of_lt (show i.val ≤ j.val from hij) hj
        change key (pad top x (liftPerm h e (Fin.castLE h ⟨i.val,hi⟩)))≤
          key (pad top x (liftPerm h e (Fin.castLE h ⟨j.val,hj⟩)))
        rw [inKey,inKey]
        exact stable.1 (show (⟨i.val,hi⟩:Fin a)≤⟨j.val,hj⟩ from hij)
      · rw [outKey j hj]
        exact greatest _
    · intro i j hij eq
      by_cases hj : j.val<a
      · have hi : i.val < a := Nat.lt_trans (show i.val < j.val from hij) hj
        let r : Fin a:=⟨i.val,hi⟩
        let s : Fin a:=⟨j.val,hj⟩
        change key (pad top x (liftPerm h e (Fin.castLE h r)))=
          key (pad top x (liftPerm h e (Fin.castLE h s))) at eq
        rw [inKey,inKey] at eq
        change push h e (Fin.castLE h r)<push h e (Fin.castLE h s)
        rw [push_inside,push_inside]
        exact stable.2 r s hij eq
      · change (push h e i).val<(push h e j).val
        simp only [push,hj]
        split
        next hi => exact lt_of_lt_of_le (e ⟨i.val,hi⟩).isLt (Nat.le_of_not_lt hj)
        next => exact hij
  rw [←shape]
  funext i
  by_cases hi : i.val<a
  · let r : Fin a:=⟨i.val,hi⟩
    change pad top x (push h e (Fin.castLE h r)) = pad top (x ∘ e) (Fin.castLE h r)
    simp [push_inside,pad,r.isLt,(e r).isLt]
  · change pad top x (push h e i)=pad top (x ∘ e) i
    simp [pad,push,hi]

end
end Hierarchy.Tagged.TerminalSort

end OAI

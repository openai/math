import OAI.Computability.BorderVNP.LabelIndex
import OAI.Computability.BorderVNP.CubeLabelISANodes

/-! # Exact incident lists in the compressed chooser directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA.LabelTrial

/-- Contents of a linked list with all its nodes in the allocated prefix. -/
def Linked (m : ℕ → ℕ) (base bound ptr : ℕ) : List Incident → Prop
  | [] => ptr = 0
  | e :: es =>
    0 < ptr ∧ ptr ≤ bound ∧ m (nodeAddr base ptr+1) = e.dir ∧
      m (nodeAddr base ptr+2) = e.other ∧ m (nodeAddr base ptr+3) = e.width ∧
      Linked m base bound (m (nodeAddr base ptr)) es

/-- A prefix-bounded list is a valid input to the chooser's physical traversal. -/
theorem Linked.chain {m base bound ptr es} (h : Linked m base bound ptr es) :
    Chain m base ptr es := by
  induction es generalizing ptr with
  | nil => exact h ▸ Chain.nil
  | cons e es ih => exact .cons h.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 (ih h.2.2.2.2.2)

/-- Agreement on all previously allocated node words preserves a list when the
allocated prefix grows. -/
theorem Linked.copy {m m' base bound bound' ptr es} (h : Linked m base bound ptr es)
    (grow : bound ≤ bound') (same : ∀ x, base ≤ x → x < base+4*bound → m' x = m x) :
    Linked m' base bound' ptr es := by
  induction es generalizing ptr with
  | nil => exact h
  | cons e es ih =>
    obtain ⟨live,room,dir,other,width,tail⟩ := h
    have he : ∀ j ≤ 3, m' (nodeAddr base ptr+j) = m (nodeAddr base ptr+j) := by
      intro j hj; apply same <;> unfold nodeAddr <;> omega
    exact ⟨live,room.trans grow,(he 1 (by decide)).trans dir,(he 2 (by decide)).trans other,
      (he 3 (by decide)).trans width,by rw [show m' (nodeAddr base ptr) = _ from he 0 (by decide)]; exact ih tail⟩

/-- A node insertion touches only its four words and its cell's head. -/
theorem push_outside (m : ℕ → ℕ) (h b n c dir o w x : ℕ)
    (off : x ≠ h+c) (skip : x < b+n*4 ∨ b+n*4+3 < x) :
    push m h b n c dir o w x = m x := by
  simp only [push,Function.update_of_ne off,Function.update_of_ne (show x ≠ b+n*4+3 by omega),
    Function.update_of_ne (show x ≠ b+n*4+2 by omega),Function.update_of_ne (show x ≠ b+n*4+1 by omega),
    Function.update_of_ne (show x ≠ b+n*4 by omega)]

/-- Prepending one row extends exactly the appropriate cell list and leaves all
other lists intact. This accounts for the orientation and the one-based links. -/
theorem push_lists {m : ℕ → ℕ} {heads base n cells c : ℕ} (e : Incident)
    {lists : ℕ → List Incident} (old : ∀ k < cells, Linked m base n (m (heads+k)) (lists k))
    (sep : heads+cells ≤ base) (hc : c < cells) (k : ℕ) (hk : k < cells) :
    let m' := push m heads base n c e.dir e.other e.width
    Linked m' base (n+1) (m' (heads+k)) (if k = c then e :: lists k else lists k) := by
  intro m'
  have same : ∀ x, base ≤ x → x < base+4*n → m' x = m x := by
    intro x hx hy; apply push_outside <;> omega
  have prev := (old k hk).copy (Nat.le_succ n) same
  by_cases eq : k = c
  · subst k
    have hb : nodeAddr base (n+1) = base+n*4 := by simp [nodeAddr,Nat.mul_comm]
    have head : m' (heads+c) = n+1 := by simp [m',push]
    rw [ite_eq_left rfl,head]
    change 0 < n+1 ∧ n+1 ≤ n+1 ∧ _
    simp only [hb]
    refine ⟨Nat.zero_lt_succ _,le_rfl,?_,?_,?_,?_⟩
    all_goals simp [m',push,Function.update,
      show base+n*4 ≠ heads+c by omega,show base+n*4+1 ≠ heads+c by omega,
      show base+n*4+2 ≠ heads+c by omega,show base+n*4+3 ≠ heads+c by omega] at *
    exact prev
  · have off : m' (heads+k) = m (heads+k) := by apply push_outside <;> omega
    simpa only [ite_eq_right eq,off] using prev

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI

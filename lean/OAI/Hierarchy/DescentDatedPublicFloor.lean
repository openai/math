import OAI.Hierarchy.DescentDatedAddressBook
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Fixed sparse date addresses for every execution of a width-indexed program -/
namespace Hierarchy.DescentDatedAddressBook
open Filter

/-- The sparse stride is part of the program. Its address formula reads no execution data. -/
def canonicalFloor (initial h K age : ℕ) := initial + age * 2^(K*h)

theorem canonicalFloor_zero (initial h K : ℕ) : canonicalFloor initial h K 0=initial := by
  simp [canonicalFloor]

theorem canonicalFloor_succ (initial h K age : ℕ) :
    canonicalFloor initial h K (age+1)=canonicalFloor initial h K age+2^(K*h) := by
  simp [canonicalFloor,Nat.add_mul,Nat.add_assoc]

theorem canonicalFloor_eq (initial h K age : ℕ) :
    canonicalFloor initial h K age=floor initial (fun _=>2^(K*h)) age := by
  induction age with
  | zero => simp [canonicalFloor,floor]
  | succ age ih => rw [canonicalFloor_succ, floor_succ, ih]

theorem canonical_room {initial h A B n : ℕ} (positive : 0<h)
    (header : initial≤2^(B*h)) (dates : n≤2^(A*h)) :
    canonicalFloor initial h B n<2^((A+B+2)*h) := by
  rw [canonicalFloor_eq]
  exact within_word positive _ header dates (fun _ _=>le_rfl)

theorem canonical_slot {base h K age words bound : ℕ}
    (used : bound≤canonicalFloor base h K age+words) (paid : words≤2^(K*h)) :
    bound≤canonicalFloor base h K (age+1) := by
  rw [canonicalFloor_succ]
  exact used.trans (Nat.add_le_add_left paid _)

/-- Quantification over arbitrary possible executions *precedes* choosing word width and
the fixed date addresses. All executions share the same absolute next-date and terminal floors. -/
theorem calendar_public_slots {choice : ℕ→Type*} {ages initial : ℕ→ℕ}
    (endAt : ∀h,choice h→Fin (ages h)→ℕ→ℕ)
    (words : ∀h,choice h × Fin (ages h)→ℕ)
    (fit : ∀h c j base,endAt h c j base≤base+words h (c,j))
    (uniform : Bounded words)
    (header : ∃B : ℕ,∀ᶠ h:ℕ in atTop,initial h≤2^(B*h))
    (dates : ∃A : ℕ,∀ᶠ h:ℕ in atTop,ages h≤2^(A*h)) :
    ∃K W : ℕ,∀ᶠ h:ℕ in atTop,
      canonicalFloor (initial h) h K (ages h)<2^(W*h) ∧
      ∀c (j : Fin (ages h)),endAt h c j (canonicalFloor (initial h) h K j.val)≤
        canonicalFloor (initial h) h K (j.val+1) := by
  obtain ⟨K,hw⟩:=uniform
  obtain ⟨B,hb⟩:=header
  obtain ⟨A,ha⟩:=dates
  refine ⟨max K B,A+max K B+2,?_⟩
  filter_upwards [hw,hb,ha,eventually_ge_atTop 1] with h lengths first count positive
  have left : 2^(K*h)≤2^(max K B*h) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (Nat.le_max_left K B))
  have right : 2^(B*h)≤2^(max K B*h) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (Nat.le_max_right K B))
  refine ⟨canonical_room (by omega) (first.trans right) count,?_⟩
  intro c j
  exact canonical_slot (fit h c j _) ((lengths (c,j)).trans left)

end Hierarchy.DescentDatedAddressBook

end OAI

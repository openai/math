import OAI.Hierarchy.TaggedSortShiftCleanup

namespace OAI
/-! # Exact sizes of the shifted and aligned physical cleanup blocks -/

noncomputable section
namespace Hierarchy.Tagged.SortLift

open scoped Classical
variable {q B : ℕ}

private theorem interval_width {n k : ℕ} (g : Fin n→Fin k) (b : Fin k)
    (lo w : ℕ) (inside : lo+w≤n)
    (members : ∀ i : Fin n,g i=b ↔ lo ≤ i.val ∧ i.val<lo+w) :
    Fintype.card (Fiber g b)=w := by
  let e : Fiber g b ≃ Fin w :=
    { toFun := fun i=>⟨i.1.val-lo,by have := (members i.1).1 i.2;omega⟩
      invFun := fun j=>⟨⟨lo+j.val,by have := j.isLt;omega⟩,(members _).2 (by
        change lo≤lo+j.val ∧ lo+j.val<lo+w;have := j.isLt;omega)⟩
      left_inv := fun i=>by
        apply Subtype.ext
        apply Fin.ext
        change lo+(i.1.val-lo)=i.1.val
        have := (members i.1).1 i.2;omega
      right_inv := fun j=>by apply Fin.ext;change lo+j.val-lo=j.val;omega }
  simpa only [Fintype.card_fin] using Fintype.card_congr e

private theorem quotient_eq {d a b : ℕ} (pos : 0<d) :
    a/d=b ↔ b*d≤a ∧ a<(b+1)*d := by
  constructor
  · intro eq
    exact ⟨(Nat.le_div_iff_mul_le pos).1 eq.ge,(Nat.div_lt_iff_lt_mul pos).1 (by omega)⟩
  · rintro ⟨lower,upper⟩
    have := (Nat.le_div_iff_mul_le pos).2 lower
    have := (Nat.div_lt_iff_lt_mul pos).2 upper
    omega

private theorem width_le_product {j : ℕ} (pos : 0<j) : B≤j*(B+B) := by
  have h : 1*(B+B)≤j*(B+B) := Nat.mul_le_mul_right (B+B) (show 1≤j from pos)
  rw [one_mul] at h
  omega

theorem aligned_exact (q B : ℕ) (pos : 0<B) (b : Fin q) :
    (aligned q B pos).length b=B+B := by
  have after := Nat.mul_le_mul_right (B+B) b.isLt
  rw [Nat.succ_mul] at after
  apply interval_width (alignedKey q B pos) b (b.val*(B+B)) (B+B) after
  intro i
  rw [Fin.ext_iff]
  change i.val/(B+B)=b.val ↔ _
  rw [quotient_eq (by omega),Nat.succ_mul]

theorem shifted_first (q B : ℕ) (pos : 0<B) (nonempty : 0<q) (b : Fin (q+1)) (first : b.val=0) :
    (shifted q B pos).length b=B := by
  apply interval_width (shiftedKey q B pos) b 0 B (by simpa using width_le_product (B:=B) nonempty)
  intro i
  rw [Fin.ext_iff]
  change (i.val+B)/(B+B)=b.val ↔ _
  rw [first,quotient_eq (by omega)]
  simp

theorem shifted_last (q B : ℕ) (pos : 0<B) (nonempty : 0<q) (b : Fin (q+1)) (last : b.val=q) :
    (shifted q B pos).length b=B := by
  have room := width_le_product (B:=B) nonempty
  apply interval_width (shiftedKey q B pos) b (q*(B+B)-B) B (by change _≤q*(B+B);omega)
  intro i
  have hi := i.isLt
  change i.val<q*(B+B) at hi
  rw [Fin.ext_iff]
  change (i.val+B)/(B+B)=b.val ↔ _
  rw [last,quotient_eq (by omega),Nat.succ_mul]
  omega

theorem shifted_interior (q B : ℕ) (pos : 0<B) (b : Fin (q+1)) (first : 0<b.val) (last : b.val<q) :
    (shifted q B pos).length b=B+B := by
  have before := width_le_product (B:=B) first
  have after := Nat.mul_le_mul_right (B+B) last
  rw [Nat.succ_mul] at after
  apply interval_width (shiftedKey q B pos) b (b.val*(B+B)-B) (B+B) (by change _≤q*(B+B);omega)
  intro i
  rw [Fin.ext_iff]
  change (i.val+B)/(B+B)=b.val ↔ _
  rw [quotient_eq (by omega),Nat.succ_mul]
  omega

theorem shifted_exact (q B : ℕ) (pos : 0<B) (nonempty : 0<q) (b : Fin (q+1)) :
    (shifted q B pos).length b=B ∨ (shifted q B pos).length b=B+B := by
  by_cases h : b.val=0
  · exact .inl (shifted_first q B pos nonempty b h)
  by_cases endp : b.val=q
  · exact .inl (shifted_last q B pos nonempty b endp)
  exact .inr (shifted_interior q B pos b (by omega) (by have := b.isLt;omega))

theorem shifted_lower (q B : ℕ) (pos : 0<B) (nonempty : 0<q) (b : Fin (q+1)) :
    B≤(shifted q B pos).length b := by rcases shifted_exact q B pos nonempty b with h|h <;> omega

end Hierarchy.Tagged.SortLift

end
end OAI

import OAI.Computability.BorderVNP.DiagonalExternalFragmentStream
import OAI.Computability.BorderVNP.DiagonalExternalFreeCell

/-! # Chronological order of positive public literal and pin pieces

The native directory numbers team, processor, field, and site step in
that order. Within one team every nonempty intersection ends before the
next one starts in the original processor bit string. In the final cell,
the same team's tile ordinals index the actual attached supplied ports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.CellAddresses Packing.Directory
open scoped Classical

private theorem pair_lt {n a b a' b' : ℕ} (hb' : b' < n) (h : n*a+b < n*a'+b') :
    a < a' ∨ a = a' ∧ b < b' := by
  have ha : a ≤ a' := by
    by_contra! ha
    have hm := Nat.mul_le_mul_left n (show a'+1 ≤ a from ha)
    rw [Nat.mul_succ] at hm
    omega
  rcases lt_or_eq_of_le ha with hlt | rfl
  · exact .inl hlt
  · exact .inr ⟨rfl,by omega⟩

/-- The raw chronological index compares exactly the source team, processor,
field and intersection step. -/
theorem live_index_order (d : Layout) {a a' : Fin d.teams} {p p' : Fin d.processors}
    {f f' : Fin d.fields} {k k' : Fin (d.literal/d.block+2)}
    (h : d.liveIndex a p f k < d.liveIndex a' p' f' k') :
    a < a' ∨ a = a' ∧ (p < p' ∨ p = p' ∧ (f < f' ∨ f = f' ∧ k < k')) := by
  unfold Layout.liveIndex at h
  simp only [Nat.add_assoc] at h
  obtain h₁ | ⟨e₁,hk⟩ := pair_lt k'.isLt (Nat.lt_of_add_lt_add_left h)
  · obtain h₂ | ⟨e₂,hf⟩ := pair_lt f'.isLt h₁
    · obtain ha | ⟨ea,hp⟩ := pair_lt p'.isLt h₂
      · exact .inl ha
      · exact .inr ⟨Fin.ext ea,.inl hp⟩
    · have ep : a = a' ∧ p = p' := by
        have eqv : finProdFinEquiv (a,p) = finProdFinEquiv (a',p') := Fin.ext (by
          change p.val+d.processors*a.val = p'.val+d.processors*a'.val
          omega)
        exact Prod.mk.inj (finProdFinEquiv.injective eqv)
      exact .inr ⟨ep.1,.inr ⟨ep.2,.inl hf⟩⟩
  · have ee : finProdFinEquiv (finProdFinEquiv (a,p),f) = finProdFinEquiv (finProdFinEquiv (a',p'),f') := by
      apply Fin.ext
      change f.val+d.fields*(p.val+d.processors*a.val) = f'.val+d.fields*(p'.val+d.processors*a'.val)
      simpa only [Nat.add_comm] using e₁
    have eqv := Prod.mk.inj (finProdFinEquiv.injective ee)
    have ep := Prod.mk.inj (finProdFinEquiv.injective eqv.1)
    exact .inr ⟨ep.1,.inr ⟨ep.2,.inr ⟨eqv.2,hk⟩⟩⟩

/-- The true source bit interval starts at the physical processor's first or
second live field and is clipped by the corresponding tile boundaries. -/
def fieldStart (r w R link : ℕ) (p : Fin r) (f : Fin 2) := p.val*(2*w+R*link)+f.val*(w+R*link)

/-- A positive clipped slice lies in both the source field and the selected tile. -/
theorem slice_bounds {a w g k : ℕ} (pos : 0 < (slice a w g k).2) :
    a ≤ (slice a w g k).1 ∧ (slice a w g k).1+(slice a w g k).2 ≤ a+w ∧
    (a/g+k)*g ≤ (slice a w g k).1 ∧ (slice a w g k).1+(slice a w g k).2 ≤ (a/g+k+1)*g := by
  dsimp only [slice] at pos ⊢
  rw [Nat.succ_mul]
  omega

/-- Both live fields end by the boundary of their processor row. -/
theorem field_end {r w R link : ℕ} (p : Fin r) (f : Fin 2) :
    fieldStart r w R link p f + w ≤ (p.val+1)*(2*w+R*link) := by
  fin_cases f <;> simp [fieldStart,Nat.succ_mul] <;> omega

/-- The lengths of true LP intersections are nonoverlapping in processor-bit
order for each team, even across adjacent fields or partial tiles. -/
theorem live_slice_order {R r w link V g entries desc : ℕ}
    {a a' : Fin (R+1)} {p p' : Fin r} {f f' : Fin 2} {k k' : Fin (w/g+2)}
    (h : (freeDirectory R r w link V g entries desc).liveIndex a p f k <
      (freeDirectory R r w link V g entries desc).liveIndex a' p' f' k')
    (first : 0 < (slice (fieldStart r w R link p f) w g k).2)
    (second : 0 < (slice (fieldStart r w R link p' f') w g k').2) :
    let x := slice (fieldStart r w R link p f) w g k
    let y := slice (fieldStart r w R link p' f') w g k'
    a < a' ∨ a = a' ∧ x.1+x.2 ≤ y.1 := by
  obtain ha | ⟨ha,hp | ⟨hp,hf | ⟨hf,hk⟩⟩⟩ := live_index_order _ h
  · exact .inl ha
  · refine .inr ⟨ha,?_⟩
    have e := (slice_bounds first).2.1.trans (field_end p f)
    have gap := Nat.mul_le_mul_right (2*w+R*link) (show p.val+1 ≤ p'.val from hp)
    exact e.trans (gap.trans ((Nat.le_add_right ..).trans (slice_bounds second).1))
  · subst p'
    have h0 : f = 0 := Fin.ext (by have := f'.isLt; change f.val < f'.val at hf; omega)
    have h1 : f' = 1 := Fin.ext (by have := f'.isLt; change f.val < f'.val at hf; omega)
    subst f
    subst f'
    have gap : fieldStart r w R link p 0+w ≤ fieldStart r w R link p 1 := by simp [fieldStart]
    exact .inr ⟨ha,(slice_bounds first).2.1.trans (gap.trans (slice_bounds second).1)⟩
  · subst p'
    subst f'
    let start := fieldStart r w R link p f
    have gap : (start/g+k.val+1)*g ≤ (start/g+k'.val)*g := by
      apply Nat.mul_le_mul_right
      change k.val < k'.val at hk
      omega
    exact .inr ⟨ha,(slice_bounds first).2.2.2.trans (gap.trans (slice_bounds second).2.2.1)⟩

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI

import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Basic

/-! # Borrowing positions for a matching inside one chunk

For every exchange, first transfer its smaller endpoint to the corresponding
position of the borrowed chunk. Conjugation by this transfer makes each
exchange cross between the two chunks.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

/-- Realize an involution supported in chunk `c` by three cross-chunk
matchings. Each borrowed position in chunk `d` is restored. -/
theorem exists_borrowed_matching {C B : Type*} [DecidableEq C] [LinearOrder B]
    (c d : C) (_hne : c ≠ d) (v : Equiv.Perm (C × B)) (hv : Function.Involutive v)
    (h : ∀ p, v p ≠ p → p.1 = c ∧ (v p).1 = c) :
    ∃ a b : Equiv.Perm (C × B),
      (∀ t ∈ [a,b], Function.Involutive t ∧ ∀ p, t p ≠ p →
        ((p.1 = c ∧ (t p).1 = d) ∨ (p.1 = d ∧ (t p).1 = c))) ∧
      ∀ p, a (b (a p)) = v p := by
  let move (p : C × B) :=
    if p.2 < (v (c,p.2)).2 then (Equiv.swap c d p.1,p.2) else p
  have hm : Function.Involutive move := by
    rintro ⟨e,i⟩
    by_cases w : i < (v (c,i)).2 <;> simp [move,w]
  let a : Equiv.Perm (C × B) := ⟨move,move,hm,hm⟩
  let b := (a.trans v).trans a
  have ha : ∀ p, a p ≠ p → (p.1 = c ∧ (a p).1 = d) ∨ (p.1 = d ∧ (a p).1 = c) := by
    rintro ⟨e,i⟩ ne
    change move (e,i) ≠ (e,i) at ne
    change (e = c ∧ (move (e,i)).1 = d) ∨ (e = d ∧ (move (e,i)).1 = c)
    by_cases w : i < (v (c,i)).2
    · by_cases ec : e = c
      · exact Or.inl ⟨ec,by simp [move,w,ec]⟩
      by_cases ed : e = d
      · exact Or.inr ⟨ed,by simp [move,w,ed]⟩
      exact False.elim (ne (by simp [move,w,Equiv.swap_apply_of_ne_of_ne ec ed]))
    · exact False.elim (ne (by simp [move,w]))
  have conjugate_cross (p q : C × B) (pq : v p = q) (ne : q ≠ p) :
      ((a p).1 = c ∧ (a q).1 = d) ∨ ((a p).1 = d ∧ (a q).1 = c) := by
    have loc := h p (pq.trans_ne ne)
    rw [pq] at loc
    rcases p with ⟨e,i⟩
    rcases q with ⟨f,j⟩
    obtain ⟨he,hf⟩ : e = c ∧ f = c := loc
    subst e
    subst f
    have qp := hv (c,i)
    rw [pq] at qp
    have ij : i ≠ j := by rintro rfl; exact ne rfl
    change ((move (c,i)).1 = c ∧ (move (c,j)).1 = d) ∨
      ((move (c,i)).1 = d ∧ (move (c,j)).1 = c)
    rcases lt_or_gt_of_ne ij with lt | gt
    · exact Or.inr (by simp [move,pq,qp,lt,not_lt_of_gt lt])
    · exact Or.inl (by simp [move,pq,qp,gt,not_lt_of_gt gt])
  refine ⟨a,b,?_,?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨hm,ha⟩
    · have aa (p : C × B) : a (a p) = p := hm p
      refine ⟨fun p => ?_, fun p ne => ?_⟩
      · change a (v (a (a (v (a p))))) = p
        rw [aa,hv,aa]
      · have ne' : v (a p) ≠ a p := by
          intro fixed
          exact ne (show a (v (a p)) = p by rw [fixed,aa])
        simpa only [aa,b,Equiv.trans_apply] using conjugate_cross (a p) (v (a p)) rfl ne'
  · intro p
    change a (a (v (a (a p)))) = v p
    rw [show ∀ z, a (a z) = z from hm,show ∀ z, a (a z) = z from hm]

end Controlled

end NearSquareRoot
end Computability
end OAI

import OAI.Computability.IntegerMultiplication.Port.Lag

/-! # Arbitrary field transpositions using the P192 opposite-wing pivot

For two fields on the same wing the pivot sequence passes through an occupied
field on the other wing and restores its original contents. There is no
requirement for a spare zero coordinate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePivot

open IntegerMultiplication.Port

variable {J : Type} [DecidableEq J] {p : ℕ}

private theorem pivot_hear (h d : J) (f : ℕ) (x : Duplex J (Tower p f)) (u : Spot J) :
    hear (Lag.fire f x (.pivot h d)) u =
      hear x (Equiv.swap (false,h) (true,d) u) := by
  by_cases e : u = (false,h)
  · simp [e,Lag.fire]
  by_cases e' : u = (true,d)
  · simp [e',Lag.fire]
  simp [Equiv.swap_apply_of_ne_of_ne e e',Lag.fire,e,e']

private theorem relay {X : Type} [DecidableEq X] {s t r : X}
    (ht : t ≠ s) (htr : t ≠ r) (u : X) :
    Equiv.swap s r (Equiv.swap r t (Equiv.swap s r u)) = Equiv.swap s t u := by
  let e := Equiv.swap s r
  have h := Equiv.congr_fun (Equiv.symm_trans_swap_trans r t e) u
  simpa [e, Equiv.swap_apply_of_ne_of_ne ht htr] using h

/-- A physical transposition with price at most three which works on all
occupied addresses for every width and restores the relay field. -/
theorem compile (r : J → ℕ) (s t : Spot J) :
    ∃ l : List (Lag J p), (∀ a ∈ l, a.legal r) ∧ (l.map Lag.prices).sum ≤ 3 ∧
      ∀ f (x : Duplex J (Tower p f)) u,
        hear (l.foldl (Lag.fire f) x) u = hear x (Equiv.swap s t u) := by
  by_cases h : s = t
  · subst t
    exact ⟨[], by simp, by simp, by simp⟩
  rcases s with ⟨_|_, i⟩ <;> rcases t with ⟨_|_, j⟩
  · refine ⟨[.pivot i i, .pivot j i, .pivot i i], by simp [Lag.legal], by simp [Lag.prices], ?_⟩
    intro f x u
    simp only [List.foldl_cons, List.foldl_nil, pivot_hear]
    rw [Equiv.swap_comm (false,j) (true,i), relay (Ne.symm h) (by simp)]
  · exact ⟨[.pivot i j], by simp [Lag.legal], by simp [Lag.prices], pivot_hear i j⟩
  · refine ⟨[.pivot j i], by simp [Lag.legal], by simp [Lag.prices], ?_⟩
    intro f x u
    rw [Equiv.swap_comm (true,i)]
    exact pivot_hear j i f x u
  · refine ⟨[.pivot i i, .pivot i j, .pivot i i], by simp [Lag.legal], by simp [Lag.prices], ?_⟩
    intro f x u
    simp only [List.foldl_cons, List.foldl_nil, pivot_hear]
    rw [Equiv.swap_comm (false,i) (true,i), relay (Ne.symm h) (by simp)]

end InterchangePivot

end NearSquareRoot
end Computability
end OAI

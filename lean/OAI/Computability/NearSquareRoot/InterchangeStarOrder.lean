import OAI.Computability.IntegerMultiplication.Port.Lag
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Max

/-!
# Moving a star centre to an extreme physical field

The H wing precedes the N wing, with both wings ordered by the supplied field
rank. One interchange moves an occupied centre to either extreme of any
finite set of selected positions, exchanging the two occupied fields.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open IntegerMultiplication.Port

variable {I J : Type} [Finite I] [DecidableEq J]

private def physicalKey (rank : J → ℕ) (s : Spot J) : Bool ×ₗ ℕ :=
  toLex (s.1, rank s.2)

omit [DecidableEq J] in
private theorem physicalKey_injective {rank : J → ℕ} (hr : Function.Injective rank) :
    Function.Injective (physicalKey rank) := by
  intro a b h
  have e := toLex.injective h
  exact Prod.ext (congrArg (Prod.fst : Bool × ℕ → Bool) e) (hr (congrArg (Prod.snd : Bool × ℕ → ℕ) e))

omit [DecidableEq J] in
private theorem early_of_key_lt {rank : J → ℕ} {s t : Spot J}
    (h : physicalKey rank s < physicalKey rank t) : Lag.early rank s t := by
  rcases s with ⟨u, i⟩
  rcases t with ⟨v, j⟩
  change toLex (u, rank i) < toLex (v, rank j) at h
  rw [Prod.Lex.toLex_lt_toLex] at h
  cases u <;> cases v <;> simp_all (config := {decide := true}) [Lag.early]

omit [Finite I] in
private theorem swap_other_slot {slot : I → Spot J} (hs : Function.Injective slot)
    (i₀ e i : I) (hi : i ≠ i₀) :
    ∃ j ≠ e, Equiv.swap (slot i₀) (slot e) (slot i) = slot j := by
  by_cases he : i = e
  · subst i
    exact ⟨i₀, hi.symm, Equiv.swap_apply_right ..⟩
  · exact ⟨i, he, Equiv.swap_apply_of_ne_of_ne (hs.ne hi) (hs.ne he)⟩

/-- Conjugating by this swap makes every gather controlled by the centre legal. -/
theorem exists_first_swap (slot : I → Spot J) (rank : J → ℕ) (i₀ : I)
    (hs : Function.Injective slot) (hr : Function.Injective rank) :
    ∃ b : Spot J, ∀ i ≠ i₀,
      Lag.early rank (Equiv.swap (slot i₀) b (slot i₀)) (Equiv.swap (slot i₀) b (slot i)) := by
  classical
  let _ := Fintype.ofFinite I
  let key := physicalKey rank ∘ slot
  have hk : Function.Injective key := (physicalKey_injective hr).comp hs
  obtain ⟨e, _, hmin⟩ := Finset.exists_min_image Finset.univ key ⟨i₀, Finset.mem_univ _⟩
  refine ⟨slot e, fun i hi => ?_⟩
  obtain ⟨j, hj, heq⟩ := swap_other_slot hs i₀ e i hi
  rw [Equiv.swap_apply_left, heq]
  exact early_of_key_lt ((hmin j (Finset.mem_univ _)).lt_of_ne (hk.ne hj.symm))

/-- Conjugating by this swap makes every gather into the centre legal. -/
theorem exists_last_swap (slot : I → Spot J) (rank : J → ℕ) (i₀ : I)
    (hs : Function.Injective slot) (hr : Function.Injective rank) :
    ∃ b : Spot J, ∀ i ≠ i₀,
      Lag.early rank (Equiv.swap (slot i₀) b (slot i)) (Equiv.swap (slot i₀) b (slot i₀)) := by
  classical
  let _ := Fintype.ofFinite I
  let key := physicalKey rank ∘ slot
  have hk : Function.Injective key := (physicalKey_injective hr).comp hs
  obtain ⟨e, _, hmax⟩ := Finset.exists_max_image Finset.univ key ⟨i₀, Finset.mem_univ _⟩
  refine ⟨slot e, fun i hi => ?_⟩
  obtain ⟨j, hj, heq⟩ := swap_other_slot hs i₀ e i hi
  rw [Equiv.swap_apply_left, heq]
  exact early_of_key_lt ((hmax j (Finset.mem_univ _)).lt_of_ne (hk.ne hj))

end Interchange

end NearSquareRoot
end Computability
end OAI

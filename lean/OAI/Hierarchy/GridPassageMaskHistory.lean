import OAI.Hierarchy.GridPassageRAMState

namespace OAI
/-! # Prefix semantics of the variable-width mark correction pass -/

namespace Hierarchy.GridPassageRAMMask
open Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing

variable {w : ℕ}

/-- Each padded chosen slot either names one mark to clear or is inactive. -/
def erased (target : ℕ → Option ℕ) (input : Memory w) : ℕ → Memory w
  | 0 => input
  | i+1 => match target i with
    | none => erased target input i
    | some a => Function.update (erased target input i) a 0

theorem erased_reads (target : ℕ → Option ℕ) (input : Memory w) (i a : ℕ) :
    erased target input i a = if ∃ s < i, target s = some a then 0 else input a := by
  classical
  induction i with
  | zero => simp [erased]
  | succ i ih =>
    have seen : (∃ s < i+1, target s = some a) ↔ (∃ s < i, target s = some a) ∨ target i = some a := by
      constructor
      · rintro ⟨s,hs,eq⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with lt|rfl
        · exact Or.inl ⟨s,lt,eq⟩
        · exact Or.inr eq
      · rintro (⟨s,hs,eq⟩ | eq)
        · exact ⟨s,hs.trans (Nat.lt_succ_self i),eq⟩
        · exact ⟨i,Nat.lt_succ_self i,eq⟩
    cases h : target i with
    | none => simpa [erased,h,seen] using ih
    | some u =>
      by_cases eu : a=u
      · subst a; simp [erased,h,seen]
      · simpa [erased,h,seen,eu,Ne.symm eu,Function.update] using ih

theorem erased_below (target : ℕ → Option ℕ) (input : Memory w) (mark i a : ℕ)
    (bounded : ∀ s < i, ∀ u, target s = some u → mark ≤ u) (ha : a<mark) : erased target input i a = input a := by
  rw [erased_reads,ite_eq_right]
  rintro ⟨s,hs,h⟩
  exact (Nat.not_le_of_lt ha) (bounded s hs a h)

end Hierarchy.GridPassageRAMMask

end OAI

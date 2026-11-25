import Mathlib.Algebra.BigOperators.Fin
import OAI.ThreeFlat.RAM.HistorySelectedNodes

namespace OAI
/-! # Exact charge for chronological expansion of a selected slot

Every compact record pays one guard scan. The linked local body runs only
at selected records, and its charge is summed only over those records.
The invariant tracks allocations and the `Stores` postcondition while
permitting the local body to clobber every hardware register.
-/

namespace ThreeFlat.RAM.HistoryNodeDirectory.Selected

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped BigOperators

variable {w p r k : ℕ}

def budget (selected : ℕ → Bool) (cost : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 6
  | n+1 => 24 + (if selected i then cost i else 0) + budget selected cost (i+1) n

theorem budget_eq (selected : ℕ → Bool) (cost : ℕ → ℕ) (i n : ℕ) :
    budget selected cost i n = 6 + 24*n + ∑ j : Fin n, if selected (i+j.val) then cost (i+j.val) else 0 := by
  induction n generalizing i with
  | zero => simp [budget]
  | succ n ih =>
    rw [budget,ih,Fin.sum_univ_succ]
    have index (j : Fin n) : i+(j.val+1)=i+1+j.val := by omega
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,index,Nat.mul_succ]
    ac_rfl

variable (M : Machine w p r k) (P : Fin 35 ↪ Fin p) (R : Fin 8 ↪ Fin r) (pub : Fin 6 → Fin k)
    (take exit : Fin p) (rom : ∀ i, M.code (P i) = rows P R pub take exit i)
    (selected : ℕ → Bool) (cost : ℕ → ℕ) (inv : ℕ → Memory w → Prop) (n : ℕ)

include rom in
/-- Full concrete forward guard loop, given the execution theorem for its
linked subtree emitter and invariants on the six public pointers. -/
theorem run (c : Config w p r) (m : Memory w) (pc : c.pc=P 0)
    (initial : inv 0 («initialize» (M.publicData∘pub) m))
    (live : ∀ i m, inv i m → (cur (M.publicData∘pub) m < m (M.publicData (pub 0)+1).val ↔ i<n))
    (which : ∀ i m, inv i m → i<n →
      (groupOK (M.publicData∘pub) m ∧ slotOK (M.publicData∘pub) m ↔ selected i = true))
    (skip : ∀ i m, inv i m → i<n → selected i=false → inv (i+1) (bump (M.publicData∘pub) m))
    (body : ∀ i c m, inv i m → i<n → selected i=true → c.pc=take →
      ∃ t≤cost i, ∃ rs out, advance M.program t c (bump (M.publicData∘pub) m) =
        some (⟨P 11,c.persistent,rs,c.privateMem⟩,out) ∧ inv (i+1) out) :
    ∃ t≤11+budget selected cost 0 n, ∃ rs out, advance M.program t c m =
      some (⟨exit,c.persistent,rs,c.privateMem⟩,out) ∧ inv n out := by
  have loop (left i : ℕ) (eq : i+left=n) (c : Config w p r) (m : Memory w) (atGuard : c.pc=P 11) (ok : inv i m) :
      ∃ t≤budget selected cost i left, ∃ rs out, advance M.program t c m =
        some (⟨exit,c.persistent,rs,c.privateMem⟩,out) ∧ inv n out := by
    induction left generalizing i c m with
    | zero =>
      have finish : i=n := by omega
      have stop := (live i m ok).not.mpr (by omega)
      have guard := check M P R pub take exit rom c m atGuard
      dsimp only [Function.comp_apply] at guard
      rw [ite_eq_right stop] at guard
      obtain ⟨rs,go⟩ := guard
      exact ⟨6,le_rfl,rs,m,go,finish ▸ ok⟩
    | succ left ih =>
      have hi : i<n := by omega
      have guard := check M P R pub take exit rom c m atGuard
      dsimp only [Function.comp_apply] at guard
      rw [ite_eq_left ((live i m ok).2 hi)] at guard
      obtain ⟨t,ht,rs,go⟩ := guard
      let mid (pc : Fin p) : Config w p r := ⟨pc,c.persistent,rs,c.privateMem⟩
      cases sel : selected i with
      | false =>
        have no := (which i m ok hi).not.mpr (by simp [sel])
        rw [ite_eq_right no] at go
        obtain ⟨b,hb,last,out,done,good⟩ := ih (i+1) (by omega) (mid (P 11)) (bump _ m) rfl (skip i m ok hi sel)
        exact ⟨t+b,by simp only [budget,sel,Bool.false_eq_true,ite_false,Nat.add_zero]; omega,last,out,advance_trans go done,good⟩
      | true =>
        rw [ite_eq_left ((which i m ok hi).2 sel)] at go
        obtain ⟨a,ha,rs',m',work,ok'⟩ := body i (mid take) m ok hi sel rfl
        obtain ⟨b,hb,last,out,done,good⟩ := ih (i+1) (by omega) ⟨P 11,c.persistent,rs',c.privateMem⟩ m' rfl ok'
        exact ⟨t+a+b,by simp only [budget,sel,ite_true]; omega,last,out,advance_trans (advance_trans go work) done,good⟩
  obtain ⟨rs,startup⟩ := start M P R pub take exit rom c m pc
  obtain ⟨b,hb,rs',out,done,ok⟩ := loop n 0 (by omega) ⟨P 11,c.persistent,rs,c.privateMem⟩ _ rfl initial
  exact ⟨11+b,by omega,rs',out,advance_trans startup done,ok⟩

end ThreeFlat.RAM.HistoryNodeDirectory.Selected

end OAI

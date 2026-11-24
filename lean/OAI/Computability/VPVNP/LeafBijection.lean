import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Matching terminal occurrences to query slots

The terminal word and the query have a label-preserving bijection of positions
exactly when they represent the same multiset. For a query with distinct labels
the bijection is unique.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseGrammar

/-- An assignment of every terminal occurrence to a distinct query slot with its label. -/
abbrev LeafBijection {V : Type*} {m : ℕ} (l : List V) (q : Fin m → V) :=
  { e : Fin l.length ≃ Fin m // ∀ i, l.get i = q (e i) }

namespace LeafBijection

private theorem exists_equiv_of_perm {V : Type*} {l r : List V} (h : l.Perm r) :
    ∃ e : Fin l.length ≃ Fin r.length, ∀ i, l.get i = r.get (e i) := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
  | @cons a l r _ ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨((finSuccEquiv l.length).trans (Equiv.optionCongr e)).trans
      (finSuccEquiv r.length).symm, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using he j
  | swap a b l =>
    let z : Fin (l.length + 2) := 0
    let o : Fin (l.length + 2) := (0 : Fin (l.length + 1)).succ
    refine ⟨Equiv.swap z o, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rw [show (0 : Fin (l.length + 2)) = z from rfl, Equiv.swap_apply_left]
      rfl
    · rw [show (0 : Fin (l.length + 1)).succ = o from rfl, Equiv.swap_apply_right]
      rfl
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp [z]) (fun h => Fin.succ_ne_zero k (Fin.succ_inj.mp h))]
      rfl
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨e, he⟩ := ih₁
    obtain ⟨f, hf⟩ := ih₂
    exact ⟨e.trans f, fun i => (he i).trans (hf (e i))⟩

/-- Assignments exist exactly for the multiset of terminals selected by the query. -/
theorem nonempty_iff {V : Type*} {m : ℕ} (l : List V) (q : Fin m → V) :
    Nonempty (LeafBijection l q) ↔
      (l : Multiset V) = (List.ofFn q : Multiset V) := by
  rw [Multiset.coe_eq_coe]
  constructor
  · rintro ⟨⟨e, he⟩⟩
    have hlen : l.length = m := by simpa using Fintype.card_congr e
    subst m
    have h : l.get = q ∘ e := funext he
    have hw : l = List.ofFn (q ∘ e) := (List.ofFn_get l).symm.trans (congrArg List.ofFn h)
    exact (congrArg (fun w => w.Perm (List.ofFn q)) hw).mpr (Equiv.Perm.ofFn_comp_perm e q)
  · intro h
    obtain ⟨e, he⟩ := exists_equiv_of_perm h
    refine ⟨⟨e.trans (finCongr List.length_ofFn), fun i => ?_⟩⟩
    exact (he i).trans (List.get_ofFn q (e i))

/-- Distinct query labels determine the assignment at every terminal occurrence. -/
theorem subsingleton_of_injective {V : Type*} {m : ℕ} (l : List V)
    {q : Fin m → V} (hq : Function.Injective q) : Subsingleton (LeafBijection l q) :=
  ⟨fun a b => Subtype.ext <| Equiv.ext fun i => hq ((a.2 i).symm.trans (b.2 i))⟩

end LeafBijection
end ParseGrammar

end VPVNP
end Computability
end OAI

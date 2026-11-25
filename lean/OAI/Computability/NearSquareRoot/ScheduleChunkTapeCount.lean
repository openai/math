import OAI.Computability.NearSquareRoot.ScheduleChunkControl
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Fixed tape overhead of the fenced wrapper

Shifting a program to registers one and above preserves the number of distinct
register names. The remaining tapes belong to the five fixed phases and the
compiler's shared return stack.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkControl

open IntegerMultiplication IntegerMultiplication.Code ChunkDispatch

private def mapSite (j : ℕ → ℕ) (l : Prog.Loc Ltr) : Prog.Loc Ltr :=
  (l.1.map (Prog.rename j), l.2.rename j)

private theorem renamed_sites (j : ℕ → ℕ) (c : Cmd) (g : Scope Ltr) :
    Prog.sites (g.map (Prog.rename j)) (c.rename j) = (Prog.sites g c).map (mapSite j) := by
  induction c generalizing g with
  | pass | push | pop | again =>
    simp [Prog.sites, Prog.rename, mapSite]
  | look i k ih =>
    simp [Prog.sites, Prog.rename, mapSite, List.map_flatMap, ih]
  | join a b ha hb =>
    simp [Prog.sites, Prog.rename, mapSite, ha, hb]
  | tie b hb =>
    simp only [Prog.rename, Prog.sites, List.map_cons, mapSite]
    congr 1
    exact hb (b::g)

private theorem shifted_name (c : Cmd) :
    Prog.touched (c.rename Nat.succ) = 0 ∨
      Prog.touched (c.rename Nat.succ) = Nat.succ (Prog.touched c) := by
  cases c <;> simp [Prog.touched,Prog.rename]

private def registers (u : List (Prog.Loc Ltr)) : Finset ℕ := (Prog.used u).toFinset

private theorem mem_registers (i : ℕ) (u : List (Prog.Loc Ltr)) :
    i ∈ registers u ↔ i = 0 ∨ ∃ l ∈ u, Prog.touched l.2 = i := by simp [registers,Prog.used]

private theorem registers_subset (d : Driver) (c : Cmd) :
    registers (area (program d c)) ⊆ registers (area (program d .pass)) ∪
      (registers (Prog.sites [] c)).image Nat.succ := by
  classical
  intro i hi
  rw [mem_registers] at hi
  rw [Finset.mem_union, mem_registers]
  rcases hi with hzero | ⟨l, hl, rfl⟩
  · exact Or.inl (Or.inl hzero)
  obtain ⟨f,_,hp⟩ := List.mem_flatMap.mp hl
  by_cases hf : f = .digit
  · subst f
    change l ∈ Prog.sites [] (c.rename Nat.succ) at hp
    rw [show Prog.sites [] (c.rename Nat.succ) = _ from renamed_sites Nat.succ c []] at hp
    obtain ⟨l',hl',rfl⟩ := List.mem_map.mp hp
    rcases shifted_name l'.2 with hz | hr
    · exact Or.inl (Or.inl hz)
    · exact Or.inr (Finset.mem_image.mpr
        ⟨Prog.touched l'.2, (mem_registers ..).mpr (Or.inr ⟨l',hl',rfl⟩), hr.symm⟩)
  · have he : program d c f = program d .pass f := by cases f <;> simp_all [program]
    rw [he] at hp
    exact Or.inl (Or.inr ⟨l, good _ f hp, rfl⟩)

private theorem card_tapes (u : List (Prog.Loc Ltr)) :
    Nat.card (Prog.Ix u) = (registers u).card + 1 := by
  classical
  let e : Prog.Idx u ≃ ↥(registers u) :=
    Equiv.subtypeEquivRight (fun i => List.mem_toFinset.symm)
  let : Fintype (Prog.Idx u) := Fintype.ofEquiv _ e.symm
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_congr e, Fintype.card_coe]

/-- The exact same additive overhead works for every candidate program,
including programs with arbitrarily sparse register names. -/
theorem tape_count_overhead (d : Driver) :
    ∃ W : ℕ, ∀ c : Cmd, Nat.card (Prog.Ix (area (program d c))) ≤
      W + Nat.card (Prog.Ix (Prog.sites [] c)) := by
  refine ⟨(registers (area (program d .pass))).card, fun c => ?_⟩
  rw [card_tapes, card_tapes, ← Nat.add_assoc]
  apply Nat.add_le_add_right
  exact (Finset.card_le_card (registers_subset d c)).trans
    ((Finset.card_union_le ..).trans (Nat.add_le_add_left Finset.card_image_le _))

/-- P192's final output copy uses exactly one more physical tape. -/
theorem output_tape_count_overhead (d : Driver) :
    ∃ W : ℕ, ∀ c : Cmd, Nat.card (Option (Prog.Ix (area (program d c)))) ≤
      W + Nat.card (Prog.Ix (Prog.sites [] c)) := by
  obtain ⟨W,h⟩ := tape_count_overhead d
  refine ⟨W+1,fun c => ?_⟩
  rw [Finite.card_option]
  have := h c
  omega

end ChunkControl

end NearSquareRoot
end Computability
end OAI

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Column coloring for the paired-terminal entropy bound -/

namespace OAI.Computability.MultitapeWeakETH

/-- One coloring of columns works for every prefix. The hypothesis is the
exact finite union bound for missing a color on a set of M extensions. -/
theorem exists_column_coloring {A P C : Type*} [Fintype A] [Fintype P] [Fintype C]
    (extensions : P → Finset A) {M : ℕ} (size : ∀ p, (extensions p).card = M)
    (budget : (Fintype.card P * Fintype.card C) *
      ((Fintype.card C - 1)^M * (Fintype.card C)^(Fintype.card A - M)) <
        (Fintype.card C)^(Fintype.card A)) :
    ∃ color : A → C, ∀ p c, ∃ a ∈ extensions p, color a = c := by
  classical
  let bad (pc : P × C) := Fintype.piFinset (fun a : A =>
    if a ∈ extensions pc.1 then Finset.univ.erase pc.2 else Finset.univ)
  have count (pc : P × C) : (bad pc).card =
      (Fintype.card C-1)^M * (Fintype.card C)^(Fintype.card A-M) := by
    simp only [bad,Fintype.card_piFinset,apply_ite Finset.card,Finset.card_erase_of_mem
      (Finset.mem_univ _),Finset.card_univ]
    rw [Finset.prod_ite]
    have complement : (Finset.univ.filter fun a => a ∉ extensions pc.1) = (extensions pc.1)ᶜ := by
      ext; simp
    simp [complement,Finset.card_compl,size]
  have bound : (Finset.univ.biUnion bad).card < (Finset.univ : Finset (A → C)).card := by
    apply Finset.card_biUnion_le.trans_lt
    simpa [count] using budget
  obtain ⟨color,_,avoids⟩ := Finset.exists_mem_notMem_of_card_lt_card bound
  refine ⟨color,fun p c => ?_⟩
  by_contra! misses
  apply avoids (Finset.mem_biUnion.mpr ⟨(p,c),Finset.mem_univ _,?_⟩)
  apply Fintype.mem_piFinset.mpr
  intro a
  by_cases ha : a ∈ extensions p <;> simp [ha,misses]

end OAI.Computability.MultitapeWeakETH

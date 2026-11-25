import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.NodupEquivFin

namespace OAI
/-! # Prefixes avoiding a family of cuts

A list of distinct slots records the order in which a multilinear monomial
acquires its factors. Its prefix sets record every cut visited in that order.
-/

namespace Hierarchy.ABPFirstCut

variable {V : Type*} [DecidableEq V]

/-- Some order of the elements of `S` avoids all the cuts in `family`. -/
def Avoids (family : Finset (Finset V)) (S : Finset V) : Prop :=
  ∃ l : List V, l.Nodup ∧ l.toFinset = S ∧ ∀ p : List V, p <+: l → p.toFinset ∉ family

/-- Every order of the full slot set has a prefix in the family. -/
def HitsEveryOrder [Fintype V] (family : Finset (Finset V)) : Prop :=
  ∀ l : List V, l.Nodup → l.toFinset = Finset.univ →
    ∃ p : List V, p <+: l ∧ p.toFinset ∈ family

variable {family : Finset (Finset V)} {S : Finset V} {i : V}

theorem avoids_empty (h : ∅ ∉ family) : Avoids family ∅ := by
  refine ⟨[], by simp, by simp, ?_⟩
  intro p hp
  simpa [List.prefix_nil.mp hp] using h

theorem avoids_not_mem (h : Avoids family S) : S ∉ family := by
  obtain ⟨l, _, rfl, hl⟩ := h
  exact hl l (List.prefix_refl _)

/-- Append the last slot to an order avoiding all earlier cuts. -/
theorem avoids_of_erase (hi : i ∈ S) (hS : S ∉ family) (h : Avoids family (S.erase i)) :
    Avoids family S := by
  obtain ⟨l, hl, he, hp⟩ := h
  have fresh : i ∉ l := by
    intro hmem
    have hm : i ∈ l.toFinset := List.mem_toFinset.mpr hmem
    rw [he] at hm
    exact Finset.notMem_erase i S hm
  have whole : (l ++ [i]).toFinset = S := by
    simpa [List.toFinset_append, he, Finset.union_comm] using Finset.insert_erase hi
  refine ⟨l ++ [i], ?_, whole, ?_⟩
  · rw [← List.concat_eq_append]
    exact (List.nodup_concat l i).mpr ⟨fresh,hl⟩
  · intro p hpref
    obtain rfl | earlier := List.prefix_concat_iff.mp hpref
    · simpa [whole] using hS
    · exact hp p earlier

theorem not_avoids_univ [Fintype V] (h : HitsEveryOrder family) : ¬Avoids family Finset.univ := by
  rintro ⟨l,hl,hs,miss⟩
  obtain ⟨p,hp,hit⟩ := h l hl hs
  exact miss p hp hit

theorem HitsEveryOrder.nonempty [Fintype V] (h : HitsEveryOrder family) : family.Nonempty := by
  let s : Finset V := Finset.univ
  obtain ⟨p, _, hp⟩ := h s.toList s.nodup_toList s.toList_toFinset
  exact ⟨p.toFinset, hp⟩

/-- Express a cut in a vertex ranking as the set of a list prefix. -/
theorem hitsEveryOrder_of_equiv [Fintype V]
    (h : ∀ ord : V ≃ Fin (Fintype.card V),
      ∃ k : ℕ, (Finset.univ.filter fun v : V => (ord v).val < k) ∈ family) :
    HitsEveryOrder family := by
  intro l hl he
  have allMem (x : V) : x ∈ l := List.mem_toFinset.mp (by simp [he])
  have length_eq : l.length = Fintype.card V := by
    simpa [he] using (List.toFinset_card_of_nodup hl).symm
  let ord := (List.Nodup.getEquivOfForallMemList l hl allMem).symm.trans (finCongr length_eq)
  obtain ⟨k,hk⟩ := h ord
  refine ⟨l.take k, List.take_prefix _ _, ?_⟩
  have prefixSet : (l.take k).toFinset = Finset.univ.filter (fun v : V => (ord v).val < k) := by
    ext v
    have idx : (ord v).val = l.idxOf v := by
      simp [ord, List.Nodup.getEquivOfForallMemList]
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and, idx]
    exact List.mem_take_iff_idxOf_lt (allMem v)
  rwa [prefixSet]

end Hierarchy.ABPFirstCut

end OAI

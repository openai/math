import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-! # Stable site order of padded public geometry records

The native sorting key consists of the physical site and the original row
ordinal. Consequently it keeps all records of one site in their original
order, even when several records carry identical payloads.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteOrder

open scoped Classical

private def score {s M : ℕ} (tag : Fin M → Fin s) (i : Fin M) :=
  (tag i).val*(2*M) + i.val

private def bucket {s M : ℕ} (tag : Fin M → Fin s) (site : Fin s) :=
  (List.finRange M).filter fun i => decide (tag i = site)

private theorem higher_score {s M : ℕ} {tag : Fin M → Fin s} {i j : Fin M} (h : tag i < tag j) :
    score tag i < score tag j := by
  have hi := i.isLt
  calc
    score tag i < ((tag i).val+1)*(2*M) := by unfold score; rw [Nat.add_mul]; omega
    _ ≤ (tag j).val*(2*M) := Nat.mul_le_mul_right _ h
    _ ≤ score tag j := Nat.le_add_right _ _

private theorem score_injective {s M : ℕ} (tag : Fin M → Fin s) : Function.Injective (score tag) := by
  intro i j he
  have hi : i.val < 2*M := by have := i.isLt; omega
  have hj : j.val < 2*M := by have := j.isLt; omega
  apply Fin.ext
  simpa [score,Nat.add_mod,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using congrArg (· % (2*M)) he

private theorem bucket_sorted {s M : ℕ} (tag : Fin M → Fin s) :
    ((List.finRange s).flatMap (bucket tag)).Pairwise (fun i j => score tag i < score tag j) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro site _
    apply ((List.pairwise_lt_finRange M).filter _).imp_of_mem
    intro i j hi hj h
    have hi' : tag i = site := by simpa [bucket] using (List.mem_filter.mp hi).2
    have hj' : tag j = site := by simpa [bucket] using (List.mem_filter.mp hj).2
    simp only [score,hi',hj',Nat.add_lt_add_iff_left]
    exact h
  · apply (List.pairwise_lt_finRange s).imp
    intro a b hab i hi j hj
    have hi' : tag i = a := by simpa [bucket] using (List.mem_filter.mp hi).2
    have hj' : tag j = b := by simpa [bucket] using (List.mem_filter.mp hj).2
    exact higher_score (hi' ▸ hj' ▸ hab)

/-- A genuine sorting permutation with the physical radix key enumerates
the same row IDs as the site-by-site stable grouping. -/
theorem sorted_ordinals {s M : ℕ} (tag : Fin M → Fin s) (π : Equiv.Perm (Fin M))
    (sorted : Monotone fun i => 2*(tag (π i)).val*M+(π i).val) :
    List.ofFn π = (List.finRange s).flatMap (fun t => (List.finRange M).filter fun i => decide (tag i = t)) := by
  let out := (List.finRange s).flatMap (bucket tag)
  have hstrict := bucket_sorted tag
  have hp : (List.ofFn π).Perm out := by
    apply (List.perm_ext_iff_of_nodup ?_ ?_).mpr
    · intro i
      have hin : i ∈ List.ofFn π := List.mem_ofFn.mpr ⟨π.symm i,π.apply_symm_apply i⟩
      have hout : i ∈ out := List.mem_flatMap.mpr ⟨tag i,List.mem_finRange _,by simp [bucket]⟩
      exact iff_of_true hin hout
    · rw [List.ofFn_eq_map]
      exact (List.nodup_finRange _).map π.injective
    · exact hstrict.imp (fun h he => by subst he; exact (lt_irrefl _ h))
  apply hp.eq_of_pairwise (le := fun i j => score tag i ≤ score tag j)
  · intro i j _ _ h₁ h₂
    exact score_injective tag (le_antisymm h₁ h₂)
  · apply List.pairwise_ofFn.mpr
    intro i j h
    simpa only [score,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using sorted h.le
  · exact hstrict.imp le_of_lt

/-- Carry any payload through the stable index sort, without needing it to be
comparable or injective. -/
theorem sorted_payloads {X : Type*} {s M : ℕ} (site : X → Fin s) (data : Fin M → X)
    (π : Equiv.Perm (Fin M)) (sorted : Monotone fun i => 2*(site (data (π i))).val*M+(π i).val) :
    List.ofFn (fun i => data (π i)) =
      (List.finRange s).flatMap fun t => (List.ofFn data).filter fun x => decide (site x = t) := by
  have h := congrArg (List.map data) (sorted_ordinals (fun i => site (data i)) π sorted)
  simpa only [List.map_ofFn,List.map_flatMap,List.ofFn_eq_map,List.filter_map,List.map_map,Function.comp_def] using h

end CellPacketGeometry.SiteOrder

end BorderVNP
end Computability
end OAI

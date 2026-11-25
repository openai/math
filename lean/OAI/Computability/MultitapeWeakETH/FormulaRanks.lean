import OAI.Computability.MultitapeWeakETH.Price
import Mathlib.Data.Fintype.EquivFin

/-! # Naming finite formula objects by a scan of their syntax keys -/

namespace OAI.Computability.MultitapeWeakETH.FormulaRanks

open scoped Classical
noncomputable section

variable {α : Type} [Fintype α] (key : α ↪ List ℕ)

private def earlier (a : α) := Finset.univ.filter (fun x => key x < key a)

private theorem strict {x y : α} (h : key x < key y) : earlier key x ⊂ earlier key y := by
  constructor
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans (Finset.mem_filter.mp ha).2 h⟩
  · intro sub
    have e := sub (show x ∈ earlier key y by simpa [earlier] using h)
    simp [earlier] at e

/-- The ordinal is the number of smaller keys. Its inverse recovers the unique
object of that rank from any complete duplicate-free listing. -/
def ordinal : α ≃ Fin (Fintype.card α) := by
  let f (a : α) : Fin (Fintype.card α) := ⟨(earlier key a).card,by
    apply lt_of_lt_of_le (Finset.card_lt_card ?_) (le_refl _ : Finset.univ.card ≤ _)
    exact ⟨Finset.subset_univ _,fun h => by
      have := h (Finset.mem_univ a)
      simp [earlier] at this⟩⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨fun x y eq => ?_,by simp⟩
  apply key.injective
  apply le_antisymm <;> by_contra! h
  · exact (Finset.card_lt_card (strict key h)).ne (congrArg Fin.val eq).symm
  · exact (Finset.card_lt_card (strict key h)).ne (congrArg Fin.val eq)

theorem ordinal_val (xs : List α) (noDup : xs.Nodup) (complete : ∀ a, a ∈ xs) (a : α) :
    (ordinal key a).val = (xs.filter fun b => decide (key b < key a)).length := by
  change (earlier key a).card = _
  rw [← List.toFinset_card_of_nodup (noDup.filter _)]
  congr 1
  ext b
  simp [earlier,complete]

omit [Fintype α] in
/-- Recover an indexing list with exactly the supplied syntax order. -/
theorem typed_list (xs : List (List ℕ)) (unique : xs.Nodup)
    (mem : ∀ x, x ∈ xs ↔ ∃ b, key b = x) :
    ∃ es : List α, es.Nodup ∧ (∀ e, e ∈ es) ∧ es.map key = xs := by
  let get (x : {x // x ∈ xs}) := ((mem x.val).mp x.property).choose
  have inv (x : {x // x ∈ xs}) : key (get x) = x.val := ((mem x.val).mp x.property).choose_spec
  let es := xs.attach.map get
  have code : es.map key = xs := by
    simp [es,List.map_map,Function.comp_def,inv]
  refine ⟨es,List.Nodup.of_map key (code ▸ unique),fun e => ?_,code⟩
  have h : key e ∈ es.map key := code ▸ (mem _).mpr ⟨e,rfl⟩
  obtain ⟨t,ht,eq⟩ := List.mem_map.mp h
  rwa [← key.injective eq]

/-- A scan can use the concrete syntax list directly, in any order. -/
theorem ordinal_keys (xs : List (List ℕ)) (unique : xs.Nodup)
    (mem : ∀ x, x ∈ xs ↔ ∃ b, key b = x) (a : α) :
    (ordinal key a).val = (xs.filter fun x => decide (x < key a)).length := by
  change (earlier key a).card = _
  rw [← List.toFinset_card_of_nodup (unique.filter _),
    ← Finset.card_image_of_injective (earlier key a) key.injective]
  congr 1
  ext x
  simp [earlier,mem]
  grind

end
end OAI.Computability.MultitapeWeakETH.FormulaRanks

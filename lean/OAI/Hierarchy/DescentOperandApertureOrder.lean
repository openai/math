import OAI.Hierarchy.DescentFallbackItemSelect

namespace OAI
/-! # The physical donor of every p-word in a chronological socket, including a boundary crossing -/
namespace Hierarchy.DescentFallbackItemSelect
open scoped Classical
noncomputable section

def rankOrder {K : ℕ} (items : Fin K→Item) (live : Finset (Fin K)) : ↥live≃Fin live.card := by
  let f : ↥live→Fin live.card := fun a=>⟨rank items live a.val,by
    apply Finset.card_lt_card
    apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
    exact ⟨a.val,a.property,by simp [before,Key.irrefl]⟩⟩
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2
    ⟨fun a b eqn=>Subtype.ext (rank_inj items a.property b.property (congrArg Fin.val eqn)),by simp⟩)

theorem rankOrder_val {K : ℕ} (items : Fin K→Item) (live : Finset (Fin K)) (j : ↥live) :
    (rankOrder items live j).val=rank items live j.val := rfl

/-- Divide an in-range word address by its batch size to read the correctly ranked original
item, including the second covered word when it crosses into the next original item. -/
theorem selected_word {K : ℕ} (items : Fin K→Item) (live : Finset (Fin K)) {m word : ℕ}
    (hm : 0<m) (fits : word<live.card*m) :
    let index : Fin live.card:=⟨word/m,(Nat.div_lt_iff_lt_mul hm).2 fits⟩
    let donor:=(rankOrder items live).symm index
    select items live (word/m)=some donor.val ∧ rank items live donor.val*m+word%m=word := by
  let index : Fin live.card:=⟨word/m,(Nat.div_lt_iff_lt_mul hm).2 fits⟩
  let donor:=(rankOrder items live).symm index
  have seen : rank items live donor.val=word/m :=
    congrArg Fin.val ((rankOrder items live).apply_symm_apply index)
  refine ⟨?_,?_⟩
  · exact (congrArg (select items live) seen.symm).trans (select_read items live donor.property)
  · change rank items live donor.val*m+word%m=word
    rw [seen,Nat.mul_comm]
    exact Nat.div_add_mod word m

theorem fits_aperture {words start offset : ℕ} (visible : offset<min 2 (words-start)) :
    start+offset<words := by omega

end
end Hierarchy.DescentFallbackItemSelect

end OAI

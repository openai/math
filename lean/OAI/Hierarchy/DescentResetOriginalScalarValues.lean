import OAI.Hierarchy.DescentResetPeerJointAuxValues

namespace OAI
/-! # Removing the self-marker and reading its original local shape -/
namespace Hierarchy.DescentResetPeerJointPacked.Aux
open DescentResetPeerJointRAM DescentResetOriginHaloRAM DescentSortedRoster DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {P N H O D : ℕ} (width : ℕ) (name : Fin N→Fin P)
    (old : Fin O→Fin D→Option (Fin O)) (near : Fin P→Fin 3→Option (Fin P)) (v : Fin H)
    (live : v.val < N) (inside : (name ⟨v.val,live⟩).val/width < O)
    (distinct : ∀r i j z,old r i=some z→ old r j=some z→i=j)

private theorem self_rank_le (r : Fin O) : before (closed old) r r ≤ D := by
  let pool:=present (closed old) r
  have member : r∈pool:=(mem_present_closed old r r).mpr (Or.inl rfl)
  have bounded : pool⊆Finset.univ.image (fun j : Fin (D+1)=>((closed old) r j).getD r) := by
    intro y hy
    obtain ⟨j,found⟩:=(Finset.mem_filter.mp hy).2
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by simp [found]⟩
  have slots : pool.card ≤ D+1:=by simpa using (Finset.card_le_card bounded).trans Finset.card_image_le
  have rank : before (closed old) r r < pool.card:=
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset ..)).mpr ⟨r,member,by simp⟩)
  omega

theorem self_bound (r : Fin O) : 1+before (closed old) r r < radix D := by
  have rank := self_rank_le old r
  have room : D+2 ≤ radix D:=Nat.le_pow_clog (by decide) _
  omega

include distinct in
theorem original_halo :
    let parent : Fin O:=⟨(name ⟨v.val,live⟩).val/width,inside⟩
    value width name old near v 0-1=before (closed old) parent parent := by
  intro parent
  rw [self_halo width name old near v live inside distinct]
  change 1+before (closed old) parent parent-1=before (closed old) parent parent
  omega

include inside distinct in
theorem original_shape :
    value width name old near v 1/radix D=(name ⟨v.val,live⟩).val%width := by
  let parent : Fin O:=⟨(name ⟨v.val,live⟩).val/width,inside⟩
  have low : 1+before (closed old) parent parent < radix D:=self_bound old parent
  have pos : 0 < radix D:=Nat.two_pow_pos _
  rw [self_joint width name old near v live inside distinct, Nat.add_assoc]
  change ((name ⟨v.val,live⟩).val%width*radix D+(1+before (closed old) parent parent))/radix D=_
  rw [Nat.mul_comm ((name ⟨v.val,live⟩).val%width) (radix D), Nat.mul_add_div pos,
    Nat.div_eq_of_lt low, Nat.add_zero]

include distinct in
theorem original_halo_digit (haloBits : ℕ) (room : D < 2^haloBits) :
    let parent : Fin O:=⟨(name ⟨v.val,live⟩).val/width,inside⟩
    ((value width name old near v 0-1 : ℕ):Cell haloBits).val=before (closed old) parent parent := by
  intro parent
  rw [original_halo width name old near v live inside distinct]
  have rank := self_rank_le old parent
  exact Fin.val_cast_of_lt (rank.trans_lt room)

include inside distinct in
theorem original_shape_digit (shortBits : ℕ) (positive : 0 < width) (room : width ≤ 2^shortBits) :
    ((value width name old near v 1/radix D : ℕ):Cell shortBits).val=(name ⟨v.val,live⟩).val%width := by
  rw [original_shape width name old near v live inside distinct]
  exact Fin.val_cast_of_lt ((Nat.mod_lt _ positive).trans_le room)

end
end Hierarchy.DescentResetPeerJointPacked.Aux

end OAI

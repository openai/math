import OAI.Hierarchy.DescentTerminalOperandSlots
import OAI.Hierarchy.DescentPackedPrivateAliases

namespace OAI
/-! # First-occurrence ranks on packed and padded operand banks -/
namespace Hierarchy.DescentLocalPrivateNames
open DescentKernelHistory DescentTerminalPointerIssue DescentTerminalChronologicalBooks
open scoped Classical BigOperators
noncomputable section
variable {Tag B : Type} (r : Recipe Tag B) {K L : ℕ}
variable (left : Slot r ↪ Fin K) (right : Slot r ↪ Fin L)

/-- Arrays with the same order on occupied operand positions select the same
original occurrence of every hidden word, even when the numeric addresses differ. -/
theorem common_first (ordered : ∀u v : Slot r,left u<left v ↔ right u<right v) (h:r.UsedWord) :
    ∃s,read r s=some h ∧ left s=firstAlias r left h ∧ right s=firstAlias r right h := by
  obtain ⟨s,hs,reads⟩:=firstAlias_read r left h
  obtain ⟨t,ht,readt⟩:=firstAlias_read r right h
  have leastL : left s≤left t := hs.symm ▸ firstAlias_le r left t h readt
  have leastR : right t≤right s := ht.symm ▸ firstAlias_le r right s h reads
  have same : right s=right t := le_antisymm (le_of_not_gt (fun lt=>leastL.not_gt ((ordered t s).2 lt))) leastR
  exact ⟨s,reads,hs,same.trans ht⟩

/-- The integer written into family seven counts distinct earlier first uses. -/
theorem common_first_ordinal (ordered : ∀u v : Slot r,left u<left v ↔ right u<right v) (h:r.UsedWord) :
    ordinal ((firstAlias r left).trans Fin.valEmbedding) h=ordinal ((firstAlias r right).trans Fin.valEmbedding) h := by
  obtain ⟨s,_,hs,ht⟩:=common_first r left right ordered h
  apply Fin.ext
  rw [ordinal_val,ordinal_val]
  apply congrArg Finset.card
  ext a
  obtain ⟨i,_,hi,hj⟩:=common_first r left right ordered a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change (firstAlias r left a).val<(firstAlias r left h).val ↔ (firstAlias r right a).val<(firstAlias r right h).val
  rw [←hs,←ht,←hi,←hj]
  exact ordered i s

private theorem birthOrdinal_mono (birth:r.Node↪ℕ) {u v:r.Node} (lt:birth u<birth v) :
    ordinal birth u<ordinal birth v := by
  change (ordinal birth u).val<(ordinal birth v).val
  rw [ordinal_val,ordinal_val]
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨u,by simp [lt],by simp⟩
  intro t ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ t,(Finset.mem_filter.mp ht).2.trans lt⟩

variable {N A : ℕ} (birth:r.Node↪ℕ) (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤A)
    (room:Fintype.card (Slot r)≤K)
local notation "rectangle" => DescentTerminalPointerIssue.slot r birth nodes arity
local notation "packed" => orderedSlots r birth room

private theorem rectangular_lt {u v:Slot r} (lt:birth u.1<birth v.1) : rectangle u<rectangle v := by
  have next_ : (ordinal birth u.1).val+1≤(ordinal birth v.1).val :=birthOrdinal_mono r birth lt
  have separated:=Nat.mul_le_mul_left A next_
  rw [Nat.mul_succ] at separated
  have short:=u.2.isLt.trans_le (arity u.1)
  change u.2.val+A*(ordinal birth u.1).val<v.2.val+A*(ordinal birth v.1).val
  omega

private theorem packed_lt {u v:Slot r} (lt:birth u.1<birth v.1) : packed u<packed v := by
  have apart:=ProtocolRAMPortRanks.prefix_disjoint r.arity birth lt
  change (packed u).val<(packed v).val
  rw [orderedSlots_val,orderedSlots_val]
  have short:=u.2.isLt
  omega

theorem rectangle_packed_order (u v:Slot r) : rectangle u<rectangle v ↔ packed u<packed v := by
  rcases lt_trichotomy (birth u.1) (birth v.1) with lt|eqn|gt
  · exact iff_of_true (rectangular_lt r birth nodes arity lt) (packed_lt r birth room lt)
  · rcases u with ⟨u,i⟩
    rcases v with ⟨v,j⟩
    obtain rfl : u=v:=birth.injective eqn
    change i.val+A*(ordinal birth u).val<j.val+A*(ordinal birth u).val ↔ (packed ⟨u,i⟩).val<(packed ⟨u,j⟩).val
    rw [orderedSlots_val,orderedSlots_val]
    simp
  · exact iff_of_false (not_lt_of_gt (rectangular_lt r birth nodes arity gt)) (not_lt_of_gt (packed_lt r birth room gt))

theorem rectangle_packed_ordinal (h:r.UsedWord) :
    ordinal ((firstAlias r rectangle).trans Fin.valEmbedding) h =
      ordinal ((firstAlias r packed).trans Fin.valEmbedding) h :=
    common_first_ordinal r rectangle packed (rectangle_packed_order r birth nodes arity room) h

end
end Hierarchy.DescentLocalPrivateNames

end OAI

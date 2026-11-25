import OAI.ThreeFlat.Diagonal.CompressorOrderIndex
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Increasing physical order of occupied party and absorbed edge bits -/

namespace ThreeFlat.Diagonal.HistoryMaskOrder

open scoped Classical BigOperators
noncomputable section

variable {a : ℕ} (active : Fin a → Prop)
local notation "mask" => Finset.univ.filter active

private def member : {i // i ∈ mask} ≃ {i // active i} where
  toFun i := ⟨i.val,(Finset.mem_filter.mp i.property).2⟩
  invFun i := ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem count : (mask).card=Fintype.card {i // active i} := by
  exact (Fintype.card_coe (mask)).symm.trans (Fintype.card_congr (member active))

/-- Both subsets have ambient size at most eight in the shrinking motif.
Only the actual role mask determines this order. -/
def order : Fin (Fintype.card {i // active i}) ≃ {i // active i} :=
  (((mask).orderIsoOfFin (count active)).toEquiv).trans (member active)

theorem ordinal (i : Fin (Fintype.card {i // active i})) :
    (Finset.univ.filter (fun j : Fin a => active j ∧ j<(order active i).val)).card=i.val := by
  have h := sorted_index mask (count active) i
  rw [←h]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

/-- A prefix sum over earlier occupied slots has no contribution from the
holes, including when the mask begins or ends with a zero-width slot. -/
theorem «prefix» (width : Fin a→ℕ) (i : Fin (Fintype.card {i // active i})) :
    (∑ j : Fin i.val, width (order active (Fin.castLE i.isLt.le j)).val) =
      ∑ b ∈ Finset.univ.filter (fun j : Fin a => active j ∧ j<(order active i).val),width b := by
  let e := (mask).orderIsoOfFin (count active)
  apply Finset.sum_bij (fun j _ => (order active (Fin.castLE i.isLt.le j)).val)
  · intro j _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,(order active _).property,?_⟩
    change e (Fin.castLE i.isLt.le j)<e i
    exact e.strictMono j.isLt
  · intro x hx y hy same
    have q := (order active).injective (Subtype.ext same)
    exact Fin.ext (congrArg (fun z : Fin (Fintype.card {k // active k}) => z.val) q)
  · intro b hb
    obtain ⟨_,yes,small⟩ := Finset.mem_filter.mp hb
    let j := (order active).symm ⟨b,yes⟩
    have val : (order active j).val=b := congrArg Subtype.val ((order active).apply_symm_apply ⟨b,yes⟩)
    have less : (j:ℕ)<i.val := by
      change j<i
      apply e.lt_iff_lt.mp
      change (order active j).val<(order active i).val
      simpa only [val] using small
    refine ⟨⟨j.val,less⟩,Finset.mem_univ _,?_⟩
    exact val
  · intro _ _
    rfl

end
end ThreeFlat.Diagonal.HistoryMaskOrder

end OAI

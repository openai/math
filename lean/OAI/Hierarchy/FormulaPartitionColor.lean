import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

namespace OAI
/-! # Coloring slots by the last member of a descending flag that contains them -/

namespace Hierarchy.FormulaPartition

open scoped Classical

variable {V : Type} [Fintype V] {t : ℕ}
   (Q : Fin (t+1) → Finset V) (full : Q 0 = Finset.univ)

private noncomputable def memberships (v : V) : Finset (Fin (t+1)) := Finset.univ.filter fun j=>v∈Q j

include full in
private theorem memberships_nonempty (v : V) : (memberships Q v).Nonempty :=
  ⟨0,by simp [memberships,full]⟩

noncomputable def chainColor (v : V) : Fin (t+1) :=
  (memberships Q v).max' (memberships_nonempty Q full v)

theorem mem_chain_iff (anti : Antitone Q) (j : Fin (t+1)) (v : V) :
    v∈Q j ↔ j≤chainColor Q full v := by
  constructor
  · intro hv
    exact Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)
  · intro le
    exact anti le ((Finset.mem_filter.mp (Finset.max'_mem (memberships Q v) (memberships_nonempty Q full v))).2)

theorem chainColor_surjective (anti : Antitone Q)
    (drop : ∀j : Fin t, (Q j.succ).card < (Q j.castSucc).card) (last : (Q (Fin.last t)).Nonempty) :
    Function.Surjective (chainColor Q full) := by
  intro j
  by_cases hj : j.val<t
  · let i : Fin t := ⟨j.val,hj⟩
    have eqn : i.castSucc=j := Fin.ext rfl
    obtain ⟨v,hin,hout⟩ := Finset.exists_mem_notMem_of_card_lt_card (drop i)
    have lo := (mem_chain_iff Q full anti i.castSucc v).mp hin
    have hi := mt (mem_chain_iff Q full anti i.succ v).mpr hout
    refine ⟨v,Fin.ext ?_⟩
    change i.val ≤ (chainColor Q full v).val at lo
    change ¬ i.val+1 ≤ (chainColor Q full v).val at hi
    change _ = i.val
    omega
  · have eqn : j = Fin.last t := Fin.ext (by have := j.isLt; change j.val=t; omega)
    obtain ⟨v,hv⟩ := last
    exact ⟨v,eqn ▸ le_antisymm (Fin.le_last _) ((mem_chain_iff Q full anti _ v).mp hv)⟩

end Hierarchy.FormulaPartition

end OAI

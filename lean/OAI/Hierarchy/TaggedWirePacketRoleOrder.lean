import OAI.Hierarchy.TaggedShorterCommonScan

namespace OAI
/-! # One public signed-packet role order, selector rows before all data -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open TaggedShorterCommonScan
open scoped Classical BigOperators

variable (E T : Type) [Fintype E] [Fintype T]

private theorem roleCard : Fintype.card (E⊕T)=Fintype.card T+Fintype.card E := by
  rw [Fintype.card_sum,Nat.add_comm]

def treeFirst : Fin (Fintype.card (E⊕T))≃E⊕T :=
  (finCongr (roleCard E T)).trans (finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Fintype.equivFin T).symm (Fintype.equivFin E).symm).trans (Equiv.sumComm T E)))

def treeOrdinal (i : Fin (Fintype.card T)) : Fin (Fintype.card (E⊕T)) :=
  (finCongr (roleCard E T)).symm (i.castAdd (Fintype.card E))

def dataOrdinal (i : Fin (Fintype.card E)) : Fin (Fintype.card (E⊕T)) :=
  (finCongr (roleCard E T)).symm (Fin.natAdd (Fintype.card T) i)

@[simp] theorem treeFirst_tree (i : Fin (Fintype.card T)) :
    treeFirst E T (treeOrdinal E T i)=.inr ((Fintype.equivFin T).symm i) := by
  simp [treeOrdinal,treeFirst]

@[simp] theorem treeFirst_data (i : Fin (Fintype.card E)) :
    treeFirst E T (dataOrdinal E T i)=.inl ((Fintype.equivFin E).symm i) := by
  simp [dataOrdinal,treeFirst]

variable {d : ℕ} (key : Fin (Fintype.card (E⊕T))→Fin d) (bits : Fin (Fintype.card (E⊕T))→ℕ)

private theorem tree_boundary (j : ℕ) (limit : j≤Fintype.card T) (g : Fin d) :
    earlier key bits j g=earlier (key ∘ treeOrdinal E T) (bits ∘ treeOrdinal E T) j g := by
  apply Finset.sum_congr rfl
  intro q mem
  have ht: q<Fintype.card T := (Finset.mem_range.mp mem).trans_le limit
  have hc: q<Fintype.card (E⊕T) := by rw [roleCard];omega
  simp only [dite_eq_left ht,dite_eq_left hc,Function.comp_apply]
  rfl

theorem tree_prefix (i : Fin (Fintype.card T)) (g : Fin d) :
    earlier key bits (treeOrdinal E T i).val g=
      earlier (key ∘ treeOrdinal E T) (bits ∘ treeOrdinal E T) i.val g :=
  tree_boundary E T key bits i.val i.isLt.le g

/-- The offset of an ordinary data bit includes *every* selector
contribution on its actual chord before the earlier data-role prefix. -/
theorem data_prefix (i : Fin (Fintype.card E)) (g : Fin d) :
    earlier key bits (dataOrdinal E T i).val g=
      earlier (key ∘ treeOrdinal E T) (bits ∘ treeOrdinal E T) (Fintype.card T) g+
        earlier (key ∘ dataOrdinal E T) (bits ∘ dataOrdinal E T) i.val g := by
  let t:=Fintype.card T
  change earlier key bits (t+i.val) g=_
  have add : earlier key bits (t+i.val) g=earlier key bits t g+
       earlier (key ∘ dataOrdinal E T) (bits ∘ dataOrdinal E T) i.val g := by
    unfold earlier
    rw [Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro q mem
    have he : q<Fintype.card E := (Finset.mem_range.mp mem).trans i.isLt
    have hc : t+q<Fintype.card (E⊕T) := by rw [roleCard];omega
    simp only [dite_eq_left he,dite_eq_left hc,Function.comp_apply]
    rfl
  rw [add,tree_boundary E T key bits t (le_refl _) g]

theorem tree_sums {q : Type} [DecidableEq q] (links : T→q) (edge : q) (width : T→ℕ) :
    (∑i : Fin (Fintype.card T),if links ((Fintype.equivFin T).symm i)=edge
        then width ((Fintype.equivFin T).symm i) else 0)=∑i : T,if links i=edge then width i else 0 :=
  (Fintype.equivFin T).symm.sum_comp (fun i=>if links i=edge then width i else 0)

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI

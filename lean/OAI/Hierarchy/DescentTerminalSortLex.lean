import OAI.Hierarchy.DescentTerminalOrder

namespace OAI
/-! # The exact stable order of the physical terminal keys -/

namespace Hierarchy.DescentTerminalSortRAM
open ProtocolRAMPortRanks Computability.BorderVNP.FragmentBucket

theorem position_lt {n k : ℕ} (old : Fin n≃Fin n) (key : Fin n→Fin k) (i j : Fin n) :
    (perm old key).symm i < (perm old key).symm j ↔
      key i < key j ∨ (key i=key j ∧ old.symm i < old.symm j) := by
  change (dest (fun a=>key (old a)) (old.symm i)).val < (dest (fun a=>key (old a)) (old.symm j)).val ↔ _
  rw [dest_lt_iff,bySite_lt_iff]
  simp only [Equiv.apply_symm_apply,Fin.val_inj]
  rfl

theorem ordered_positions {n e o s : ℕ} (edge : Fin n→Fin e) (ordinal : Fin n→Fin o)
    (side : Fin n→Fin s) (i j : Fin n) :
    (order edge ordinal side).symm i < (order edge ordinal side).symm j ↔
      edge i<edge j ∨ edge i=edge j ∧ (ordinal i<ordinal j ∨ ordinal i=ordinal j ∧
        (side i<side j ∨ side i=side j ∧ i<j)) := by
  simp only [order,position_lt,Equiv.refl_symm,Equiv.refl_apply]

theorem sorted_pair {n e o s : ℕ} (edge : Fin n→Fin e) (ordinal : Fin n→Fin o)
    (side : Fin n→Fin s) (i j : Fin n) (early : i<j) :
    let t:=order edge ordinal side
    edge (t i)<edge (t j) ∨ edge (t i)=edge (t j) ∧
      (ordinal (t i)<ordinal (t j) ∨ ordinal (t i)=ordinal (t j) ∧
      (side (t i)<side (t j) ∨ side (t i)=side (t j) ∧ t i<t j)) := by
  apply (ordered_positions edge ordinal side _ _).mp
  simpa using early

end Hierarchy.DescentTerminalSortRAM

end OAI

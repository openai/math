import OAI.Hierarchy.FormulaPartitionRank
import OAI.Hierarchy.FormulaPartitionThreshold
import OAI.Hierarchy.SlotChains
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Counting the slot partitions with admissible halving thresholds -/

namespace Hierarchy.FormulaPartition

open FormulaSlotChains FormulaPartitionRank
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] {t : ℕ}
local notation "d" => Fintype.card V

def colorTail (π : Partition V (t+1)) (j : Fin (t+1)) : Finset V :=
  Finset.univ.filter fun v=>j≤π.val v

@[simp] theorem mem_colorTail (π : Partition V (t+1)) (j : Fin (t+1)) (v : V) :
    v∈colorTail π j ↔ j≤π.val v := by simp [colorTail]

def admissiblePartitions (V : Type) [Fintype V] (t : ℕ) : Finset (Partition V (t+1)) :=
  Finset.univ.filter fun π => ∀j, (colorTail π j).card ≤ threshold (Fintype.card V) j.val

private def encode (π : Partition V (t+1)) := List.ofFn fun j : Fin t => colorTail π j.succ

private theorem encode_injective : Function.Injective (encode (V:=V) (t:=t)) := by
  intro π ρ eqn
  have eqSlots : (fun j : Fin t => colorTail π j.succ) = (fun j : Fin t => colorTail ρ j.succ) :=
    List.ofFn_inj.mp eqn
  have same (j : Fin (t+1)) : colorTail π j = colorTail ρ j := by
    refine Fin.cases ?_ (fun i=>congrFun eqSlots i) j
    simp [colorTail]
  have transfer (v : V) (j : Fin (t+1)) : j≤π.val v ↔ j≤ρ.val v := by
    simpa only [mem_colorTail] using
      (show v∈colorTail π j ↔ v∈colorTail ρ j by rw [same])
  apply Subtype.ext
  funext v
  exact le_antisymm ((transfer v (π.val v)).mp le_rfl) ((transfer v (ρ.val v)).mpr le_rfl)

omit [Fintype V] in
private theorem fits_ofFn {k : ℕ} (Q : Fin (k+1)→Finset V) (c : Fin k → ℕ)
    (shrink : ∀ j : Fin k, Q j.succ ⊆ Q j.castSucc)
    (sizes : ∀ j : Fin k, (Q j.succ).card ≤ c j) :
    Fits (Q 0) (List.ofFn c) (List.ofFn fun j : Fin k => Q j.succ) := by
  induction k with
  | zero => simp [Fits]
  | succ k ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    exact ⟨shrink 0,sizes 0,
      ih (fun j=>Q j.succ) (fun j=>c j.succ) (fun j=>shrink j.succ) (fun j=>sizes j.succ)⟩

theorem card_admissiblePartitions (V : Type) [Fintype V] (t : ℕ) :
    (admissiblePartitions V t).card ≤ 2^(2*Fintype.card V) := by
  classical
  let c (j : Fin t) := threshold (Fintype.card V) (j.val+1)
  have caps : List.ofFn c = tailCaps (Fintype.card V) t := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have h : i<t := by simpa using hi
    simpa only [List.getElem_ofFn,c,threshold] using
      (getElem_tailCaps (Fintype.card V) t ⟨i,h⟩).symm
  let S := slotChains (Finset.univ : Finset V) (tailCaps (Fintype.card V) t)
  have into (π : Partition V (t+1)) (hπ : π∈admissiblePartitions V t) : encode π∈S := by
    apply (mem_slotChains ..).mpr
    rw [←caps]
    have accepted := (Finset.mem_filter.mp hπ).2
    have fits := fits_ofFn (colorTail π) c (fun j v hv => (mem_colorTail ..).mpr
      ((Fin.castSucc_lt_succ (i:=j)).le.trans ((mem_colorTail ..).mp hv))) (fun j=>accepted j.succ)
    simpa [colorTail,encode,Fin.zero_le] using fits
  have bound := Finset.card_le_card_of_injOn encode (fun _ hp=>into _ hp) encode_injective.injOn
  exact bound.trans (by simpa [S] using card_marked_chains (Finset.univ : Finset V) t)

end
end Hierarchy.FormulaPartition

end OAI

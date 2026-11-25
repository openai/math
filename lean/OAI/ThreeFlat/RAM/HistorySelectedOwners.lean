import OAI.ThreeFlat.RAM.HistorySelectedSweep

namespace OAI
/-! # The forward guard reads the terminal owner of each chronological node -/

namespace ThreeFlat.RAM.HistoryNodeDirectory.Selected

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing BigOperators

variable {w n : ℕ} (d : Data w)

structure Directory (w n : ℕ) where
  root : Fin n → Word w
  owner : Word w → Word w × Word w
  group : Word w
  slot : Word w

variable (D : Directory w n)

/-- Only addresses touched by actual roots are required in the owner bank. -/
def addresses (i : Fin n) : Fin 5 → Word w :=
  let root := D.root i
  let owner := d 2+(root+root)
  ![d 1+(i.val:Word w),owner,owner+1,d 3,d 3+3]

def contents (i : Fin n) : Fin 5 → Word w :=
  ![D.root i,(D.owner (D.root i)).1,(D.owner (D.root i)).2,D.group,D.slot]

def Recorded (m : Memory w) := ∀ i j, m (addresses d D i j).val = contents D i j

def picked (i : ℕ) : Bool := if h : i<n then decide (D.owner (D.root ⟨i,h⟩)=(D.group,D.slot)) else false

/-- After incrementing the temporary cursor, the directory scans retain all
live owner, root, group and slot words. -/
theorem recorded_bump (m : Memory w) (H : Recorded d D m) (apart : ∀ i j, addresses d D i j ≠ d 0) :
    Recorded d D (bump d m) := by
  intro i j
  change (if (addresses d D i j).val=(d 0).val then _ else _) = _
  rw [ite_eq_right (fun e=>apart i j (Fin.ext e))]
  exact H i j

/-- The guard predicate in the actual 35-instruction forward scan is the
requested group and slot equality on the already computed terminal roots. -/
theorem guards (i : Fin n) (m : Memory w) (H : Recorded d D (bump d m)) (here : cur d m = (i.val : Word w)) :
    groupOK d m ∧ slotOK d m ↔ picked D i.val=true := by
  have root : bump d m (d 1+cur d m).val = D.root i := by simpa [addresses,contents,here] using H i 0
  have own : owner d m = d 2+(D.root i+D.root i) := by simp [owner,root]
  have group : bump d m (d 3).val=D.group := by simpa [addresses,contents] using H i 3
  have slot : bump d m (d 3+3).val=D.slot := by simpa [addresses,contents] using H i 4
  have a : bump d m (owner d m).val=(D.owner (D.root i)).1 := by simpa [own,addresses,contents] using H i 1
  have b : bump d m (owner d m+1).val=(D.owner (D.root i)).2 := by simpa [own,addresses,contents] using H i 2
  unfold groupOK slotOK
  rw [group,slot,a,b]
  simp only [picked,dite_eq_left i.isLt,decide_eq_true_eq]
  constructor
  · rintro ⟨hg,hs⟩
    exact Prod.ext hg.symm hs.symm
  · intro pair
    exact ⟨(congrArg Prod.fst pair).symm,(congrArg Prod.snd pair).symm⟩

/-- Assigning the sum of chronological costs to each root charges exactly
its descendants during a single scheduled slot sweep. -/
theorem cost_fiber (cost : Fin n → ℕ) :
    (∑ i : Fin n, if picked D i.val then cost i else 0) =
      ∑ root : Word w, if D.owner root=(D.group,D.slot) then
        ∑ i : {j : Fin n // D.root j=root}, cost i.val else 0 := by
  classical
  rw [←Fintype.sum_fiberwise D.root (fun i => if picked D i.val then cost i else 0)]
  apply Finset.sum_congr rfl
  intro root _
  by_cases h : D.owner root=(D.group,D.slot)
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro i _
    have stored : D.owner (D.root i.val)=(D.group,D.slot):=i.property.symm ▸ h
    simp [picked,i.val.isLt,stored]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro i _
    have stored : D.owner (D.root i.val)≠(D.group,D.slot):=i.property.symm ▸ h
    simp [picked,i.val.isLt,stored]

end ThreeFlat.RAM.HistoryNodeDirectory.Selected

end OAI

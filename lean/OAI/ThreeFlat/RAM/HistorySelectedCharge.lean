import OAI.ThreeFlat.RAM.HistorySelectedProcedure
import OAI.ThreeFlat.RAM.HistorySelectedOwners

namespace OAI
/-! # Selected-node preparation charges from the physical terminal-owner directory -/

namespace ThreeFlat.RAM.HistoryNodeDirectory.Selected

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open scoped BigOperators Fin.CommRing

variable {w n : ℕ}

/-- An owner-table traversal pays a fixed chronological scan plus the cost
of descendants of exactly the terminal cells assigned to this team/slot. -/
theorem procedure_owners (data : Data w) (A : Procedure w) (D : Directory w n) (cost : ℕ → ℕ)
    (pre : Memory w → Prop) (inv : Memory w → ℕ → Memory w → Prop)
    (initial : ∀ input, pre input → inv input 0 («initialize» data input))
    (cursor : ∀ input i m, inv input i m → (cur data m).val=i ∧ (m (data 0+1).val).val=n)
    (ownerTable : ∀ input i m, inv input i m → Recorded data D m)
    (apart : ∀ i j, addresses data D i j ≠ data 0)
    (skip : ∀ input i m, inv input i m → i<n → picked D i=false → inv input (i+1) (bump data m))
    (body : ∀ input i, pre input → i<n → picked D i=true →
      A.Spec (fun x => ∃ m, inv input i m ∧ x=bump data m)
        (fun _ out => inv input (i+1) out) (cost i)) :
    (procedure data A).Spec pre (fun input out => inv input n out)
      (17+24*n+ ∑ root : Word w, if D.owner root=(D.group,D.slot) then
        ∑ j : {i : Fin n // D.root i=root}, cost j.val.val else 0) := by
  have ready := procedure_spec data A n (picked D) cost pre inv initial
  have live (input : Memory w) (i : ℕ) (m : Memory w) (h : inv input i m) :
      cur data m < m (data 0+1).val ↔ i<n := by
    obtain ⟨step,last⟩ := cursor input i m h
    change (cur data m).val < (m (data 0+1).val).val ↔ i<n
    rw [step,last]
  have selected (input : Memory w) (i : ℕ) (m : Memory w) (h : inv input i m) (hi : i<n) :
      groupOK data m ∧ slotOK data m ↔ picked D i=true := by
    have atIndex : cur data m = (i : Word w) := by
      rw [← (cursor input i m h).1]
      exact (Fin.cast_val_eq_self _).symm
    exact guards data D ⟨i,hi⟩ m (recorded_bump data D m (ownerTable input i m h) apart) atIndex
  have h : (procedure data A).Spec pre (fun input out => inv input n out)
      (11+budget (picked D) cost 0 n) := ready live selected skip body
  have fuel := cost_fiber D (fun i => cost i.val)
  rw [budget_eq] at h
  simp only [Nat.zero_add] at h
  rw [fuel] at h
  have normalized (total : ℕ) : 11+(6+24*n+total)=17+24*n+total := by omega
  rw [normalized] at h
  exact @h

end ThreeFlat.RAM.HistoryNodeDirectory.Selected

end OAI

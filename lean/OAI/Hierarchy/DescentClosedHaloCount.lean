import OAI.Hierarchy.DescentClosedPeerTable
import OAI.Hierarchy.DescentSortedRoster
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI
/-! # Rank in the closed old-host halo using one test per physical port -/
namespace Hierarchy.DescentResetOriginHaloRAM
open DescentSortedRoster
open scoped BigOperators
noncomputable section

variable {H D : ℕ} (p : Fin H → Fin D → Option (Fin H))

theorem mem_present_closed (r z : Fin H) :
    z ∈ present (closed p) r ↔ z = r ∨ ∃ i, p r i = some z := by
  change z ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hit⟩
    induction i using Fin.lastCases with
    | last => left; exact (Option.some.inj (by simpa only [closed,Fin.lastCases_last] using hit)).symm
    | cast i => right; exact ⟨i,by simpa only [closed,Fin.lastCases_castSucc] using hit⟩
  · rintro (rfl | ⟨i,hit⟩)
    · exact ⟨Fin.last D,by simp [closed]⟩
    · exact ⟨i.castSucc,by simpa only [closed,Fin.lastCases_castSucc] using hit⟩

theorem before_closed (distinct : ∀ r i j z, p r i = some z → p r j = some z → i = j)
    (r z : Fin H) :
    before (closed p) r z = (if r < z then 1 else 0) +
      ∑ i, if (p r i).any (fun q => q ≠ r ∧ q < z) then 1 else 0 := by
  classical
  let old := (present (closed p) r).filter (· < z)
  let hits (i : Fin D) := (p r i).any (fun q => q ≠ r ∧ q < z)
  let target (i : Fin D) := (p r i).getD r
  let ports := Finset.univ.filter (fun i => hits i = true)
  have accepted (i : Fin D) (hi : i ∈ ports) :
      p r i = some (target i) ∧ target i ≠ r ∧ target i < z := by
    have h := (Finset.mem_filter.mp hi).2
    cases e : p r i with
    | none => simp [hits,e] at h
    | some q =>
      have ok : q ≠ r ∧ q < z := by simpa [hits,e] using h
      simpa [target,e] using ok
  have card : ports.card = (old.erase r).card := by
    apply Finset.card_bij (fun i _ => target i)
    · intro i hi
      obtain ⟨hit,other,less⟩ := accepted i hi
      exact Finset.mem_erase.mpr ⟨other,Finset.mem_filter.mpr
        ⟨(mem_present_closed p r _).mpr (.inr ⟨i,hit⟩),less⟩⟩
    · intro i hi j hj eqn
      exact distinct r i j _ ((accepted i hi).1.trans (congrArg some eqn)) (accepted j hj).1
    · intro q hq
      obtain ⟨other,inside⟩ := Finset.mem_erase.mp hq
      obtain ⟨member,less⟩ := Finset.mem_filter.mp inside
      obtain ⟨i,hit⟩ := ((mem_present_closed p r q).mp member).resolve_left other
      exact ⟨i,by simp [ports,hits,hit,other,less],by simp [target,hit]⟩
  change old.card = (if r < z then 1 else 0) + ∑ i, if hits i then 1 else 0
  have count : (∑ i, if hits i then 1 else 0 : ℕ) = ports.card := by simp [ports]
  rw [count,card]
  by_cases lt : r < z
  · have inside : r ∈ old := Finset.mem_filter.mpr ⟨(mem_present_closed p r r).mpr (.inl rfl),lt⟩
    rw [ite_eq_left lt,Nat.add_comm]
    exact (Finset.card_erase_add_one inside).symm
  · have outside : r ∉ old := fun h => lt (Finset.mem_filter.mp h).2
    simp [lt,Finset.erase_eq_of_notMem outside]

end
end Hierarchy.DescentResetOriginHaloRAM

end OAI

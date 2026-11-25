import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Consecutive indices of the positions with a given common home -/
namespace Hierarchy.DescentTerminalCohortRanks
open Computability.BorderVNP.FragmentBucket Computability.BorderVNP.Crossing.Profile ProtocolRAMPortRanks
open scoped Classical BigOperators
noncomputable section

def numbered {n H : ℕ} (home:Fin n→Fin H) (v:Fin H) : {j // home j=v} ≃ Fin (count home v) :=
  ((slots home v rfl).toEquiv.trans
    (Equiv.subtypeEquivRight fun i=>by simp [positions] : positions home v ≃ {i // home i=v})).symm

theorem numbered_read {n H : ℕ} (home:Fin n→Fin H) (v:Fin H) (z : {j // home j=v}) :
    (numbered home v z).val=prior home z.val.val v := by
  obtain ⟨i,rfl⟩:=(numbered home v).symm.surjective z
  rw [Equiv.apply_symm_apply]
  exact (prefixCount_slot home rfl v i).symm

end
end Hierarchy.DescentTerminalCohortRanks

end OAI

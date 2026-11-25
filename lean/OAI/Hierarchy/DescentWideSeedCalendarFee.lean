import OAI.Hierarchy.DescentTerminalEpochBits
import OAI.Hierarchy.DescentProfileSeatCalendar
import OAI.Hierarchy.DescentSeedTokenNumbers

namespace OAI
/-! # Word mass of the original packed selector and its charge at the initial date -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentSIMDLookup
noncomputable section
def unit (C : ℕ) := DescentTerminalEpochBits.width C+1
def grain (w C : ℕ) := lanes w (unit C)
end
end Hierarchy.DescentPackedEpochShelves

namespace Hierarchy.DescentWideSeedFlags
open DescentCompiler DescentCompiler.TerminalScale DescentPackedEpochShelves DescentSeedRoot
open scoped Classical BigOperators
noncomputable section

/-- The seed digit loss is linear in the date age even when the payload is many bits wide. -/
theorem seed_digits {h s B : ℕ} (word : s ≤ h) (positive : 0 < B) :
    digitsNeeded s≤2*B*(Nat.log 2 h/(2*B)+1) := by
  unfold digitsNeeded
  rw [Nat.log2_eq_log_two]
  have small:=Nat.log_mono_right (b:=2) word
  have past:=Nat.lt_mul_div_succ (Nat.log 2 h) (by omega : 0<2*B)
  omega

variable (S : AtomSchedule)
local notation "rate" => (S.rounds+1)*(S.hostGain+S.capGain+1)+11
def originalBill (S : AtomSchedule) (C B h : ℕ) :=
  328*S.initialSites*h+(1920*B+48*unit C)*(S.hostSize 0*(S.groupCount 0*S.radix))*scale S.height
    ((S.rounds+1)*(S.hostGain+S.capGain+1)+11)

def dateFee (C B h : ℕ) (i : Fin (S.length+1)) := if i.val=0 then originalBill S C B h else 0

theorem dateFee_room (C B h : ℕ) (i : Fin (S.length+1)) :
    dateFee S C B h i ≤ S.hostSize i.val*h*328+S.hostSize i.val*(S.groupCount i.val*S.radix)*
      (scale S.height rate*(1920*B+48*unit C)) := by
  by_cases date : i.val=0
  · rw [dateFee,ite_eq_left date,date,originalBill]
    dsimp [AtomSchedule.hostSize]
    simp only [Nat.mul_one]
    apply le_of_eq;ring
  · simp [dateFee,date]

theorem dateFee_sum (C B h : ℕ) : ∑i : Fin (S.length+1),dateFee S C B h i=originalBill S C B h := by
  simp [dateFee,show ∀i : Fin (S.length+1),i.val=0 ↔ i=0 from fun i=>⟨fun q=>Fin.ext q,fun q=>by rw [q];rfl⟩]

end
end Hierarchy.DescentWideSeedFlags

end OAI

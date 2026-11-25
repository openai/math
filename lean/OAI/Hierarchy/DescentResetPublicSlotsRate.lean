import OAI.Hierarchy.DescentResetRosterFunctions
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Dated candidate capacity including the complete contact and private cable rosters -/
noncomputable section
namespace Hierarchy.DescentResetLocalRoster
open DescentCompiler.TerminalScale
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d)

def cableFactor (ht : ℕ) :=
  4*(2^n+2)*(2^n+2^ht+DescentResetCableSlots.cableCap board ht)

theorem public_slots_exact (ht k cap : ℕ) :
    publicSlots board ht k cap =
      4*2^k*cap+1+cableFactor board ht*2^k := by
  unfold publicSlots rootSlots cableFactor
  rw [pow_succ]
  ring

theorem public_slots_volume (ht k cap E : ℕ) (one : 1≤E) (blocks : 2^k≤E) (capacity : cap≤E) :
    publicSlots board ht k cap ≤ (5+cableFactor board ht)*E^2 := by
  rw [public_slots_exact]
  have sq : E≤E^2 := by simpa only [pow_two,one_mul] using Nat.mul_le_mul_right E one
  have prod : 2^k*cap≤E^2 := by simpa only [pow_two] using Nat.mul_le_mul blocks capacity
  have contact := Nat.mul_le_mul_left (cableFactor board ht) (blocks.trans sq)
  nlinarith only [one.trans sq,prod,contact]

theorem public_slots_rate (ht r : ℕ) :
    ∃e,∀j k cap, 2^k≤ scale j r → cap≤ scale j r →
      publicSlots board ht k cap ≤ scale j e ∧ cap≤ scale j e := by
  let C := 5+cableFactor board ht
  refine ⟨C+2*r,?_⟩
  intro j k cap blocks capacity
  have fixed : C≤2^(C*(j+1)) :=
    (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  have one : 1≤ scale j r := Nat.two_pow_pos _
  constructor
  · apply (public_slots_volume board ht k cap (scale j r) one blocks capacity).trans
    change C*(scale j r)^2 ≤ scale j (C+2*r)
    calc
      C*(scale j r)^2 ≤ 2^(C*(j+1))*(scale j r)^2 := Nat.mul_le_mul_right _ fixed
      _ = scale j (C+2*r) := by
        unfold scale
        rw [←pow_mul,←pow_add]
        congr 1
        ring
  · exact capacity.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right (j+1) (by omega)))

end Hierarchy.DescentResetLocalRoster
end

end OAI

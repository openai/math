import OAI.Computability.BorderVNP.CubeLabelISAProgram
import OAI.Computability.BorderVNP.CubeMeanClock

/-! # Closed sparse tick count for the public label pass

All terms involving the number of cable descriptors add over the incidence
lists. The remaining terms are charged once per cell or once for setup.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Finset

/-- Allowance for scoring one candidate on the cache and its incident lists. -/
def scoreTicks (Z degree : ℕ) := (Z^2+Z)*(24*degree+18)+3

/-- Allowance for committing the least minimizing candidate on the same bins. -/
def commitTicks (Z degree : ℕ) := (Z^2+Z)*(24*degree+18)+2

/-- The fitted scoring and commit allowances in one complete iteration, including
its loop guard. The dependence on the number of incident descriptors is linear. -/
theorem cellTicks_exact (z c : ℕ) (degree : ℕ → ℕ) :
    cellTicks z (fun i => scoreTicks (z+1) (degree i)) (fun i => commitTicks (z+1) (degree i)) c =
      let Z := z+1
      let G := Z^2+Z
      24*(Z+1)*G*degree c + (18*(Z+1)*G+8*Z+11) := by
  dsimp [cellTicks,scoreTicks,commitTicks]
  ring

/-- Complete allowance for the setup, ordinal loop, and terminating guard. -/
def assignmentTicks (setupSlots z cells : ℕ) (degree : ℕ → ℕ) : ℕ :=
  setupSlots + ((∑ c ∈ Ico 0 cells,
    cellTicks z (fun i => scoreTicks (z+1) (degree i)) (fun i => commitTicks (z+1) (degree i)) c)+1)

/-- The loop's allowance is an explicit affine function of the number of cells
and the total number of incidences, with no maximal-degree replacement. -/
theorem assignmentTicks_exact (setupSlots z cells : ℕ) (degree : ℕ → ℕ) :
    assignmentTicks setupSlots z cells degree =
      let Z := z+1
      let G := Z^2+Z
      setupSlots+1 + 24*(Z+1)*G*(∑ c ∈ range cells, degree c) +
        (18*(Z+1)*G+8*Z+11)*cells := by
  simp only [assignmentTicks,cellTicks_exact,Nat.Ico_zero_eq_range,sum_add_distrib,
    ← mul_sum, sum_const,card_range,smul_eq_mul]
  ring

private theorem coefficients (Z : ℕ) :
    24*(Z+1)*(Z^2+Z) ≤ 200*(Z+1)^3 ∧ 18*(Z+1)*(Z^2+Z)+8*Z+11 ≤ 200*(Z+1)^3 := by
  constructor <;> nlinarith only [Nat.zero_le (Z^3), Nat.zero_le (Z^2), Nat.zero_le Z]

/-- A fixed setup of fewer than 200 slots and the sparse public scan together
fit a cubic alphabet factor times one plus the cell and incidence counts. -/
theorem assignmentTicks_le {setupSlots : ℕ} (hs : setupSlots < 200) (z cells : ℕ) (degree : ℕ → ℕ) :
    assignmentTicks setupSlots z cells degree ≤
      200*(1+cells+(∑ c ∈ range cells, degree c))*((z+1)+1)^3 := by
  rw [assignmentTicks_exact]
  let Z := z+1
  let D := ∑ c ∈ range cells, degree c
  have hz : 1 ≤ (Z+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hsetup : setupSlots+1 ≤ 200*(Z+1)^3 := Nat.le_trans hs (Nat.le_mul_of_pos_right _ hz)
  obtain ⟨hd,hc⟩ := coefficients Z
  calc
    _ ≤ 200*(Z+1)^3 + 200*(Z+1)^3*D + 200*(Z+1)^3*cells :=
      Nat.add_le_add (Nat.add_le_add hsetup (Nat.mul_le_mul_right _ hd)) (Nat.mul_le_mul_right _ hc)
    _ = _ := by dsimp [Z,D]; ring

/-- The same complete program fits the manuscript's previously established
asymptotic clock when all degrees are bounded by the indicated sparse cap. -/
theorem assignmentTicks_le_scanEnvelope {setupSlots : ℕ} (hs : setupSlots < 200) (z cells cap : ℕ)
    (degree : ℕ → ℕ) (bounded : ∀ c < cells, degree c ≤ cap) :
    assignmentTicks setupSlots z cells degree ≤ Cube.MeanChoice.scanEnvelope 200 cells cap (z+1) := by
  have total : (∑ c ∈ range cells, degree c) ≤ cells*cap := by
    calc
      _ ≤ ∑ _c ∈ range cells, cap := sum_le_sum fun c hc => bounded c (mem_range.mp hc)
      _ = _ := by simp
  apply (assignmentTicks_le hs z cells degree).trans
  unfold Cube.MeanChoice.scanEnvelope
  have rows : 1+cells+(∑ c ∈ range cells, degree c) ≤ (cells+1)*(cap+1) := by
    rw [Nat.add_mul,Nat.mul_add,one_mul]
    omega
  calc
    _ ≤ 200*((cells+1)*(cap+1))*((z+1)+1)^6 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ rows) (Nat.pow_le_pow_right (by omega) (by decide))
    _ = _ := by ring

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI

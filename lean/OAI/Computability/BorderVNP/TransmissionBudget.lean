import OAI.Computability.BorderVNP.TransmissionModel

/-! # Uniform time constants for reading public ranges and their incident bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- An unrelated team pays only the descriptor overhead; an incident team scans its width
once even if both endpoints are local. -/
def Range.incident (row : Range w) (team : Word w) : ℕ :=
  if team = row.teamA ∨ team = row.teamB then row.width.val else 0

/-- The longest single-bit handler, including the full addressed two-hop calculation,
fits in a fixed 256-slot budget. -/
theorem bitCode_budget (mode : Role) : mode.bitCode.slots+2 ≤ 256 := by cases mode <;> decide

/-- Executing the payload on one team costs a constant times its incident bit width. -/
theorem Range.teamCost_le (row : Range w) (team : Word w) : row.teamCost team ≤ 256*row.incident team := by
  by_cases h : team = row.teamA ∨ team = row.teamB
  · rw [Range.teamCost,Range.incident,ite_eq_left h]
    cases row.selected team with
    | none => exact Nat.zero_le _
    | some role =>
      cases role with
      | none => exact Nat.zero_le _
      | some mode =>
        exact (Nat.mul_le_mul_left _ (bitCode_budget mode)).trans_eq (Nat.mul_comm ..)
  · have ha : team ≠ row.teamA := fun he => h (.inl he)
    have hb : team ≠ row.teamB := fun he => h (.inr he)
    have hs : row.selected team =
        if row.kind = 0 then some none else if row.kind = 1 then some none else none := by
      change (if row.kind = 0 then
        (if team = row.teamA then (if row.teamA=row.teamB then some (some Role.sharedHere) else some (some Role.receiveA))
         else if team=row.teamB then some (some Role.receiveB) else some none) else
         if row.kind=1 then (if team=row.teamA then (if row.teamA=row.teamB then some (some Role.dataHere) else some (some Role.sendData))
          else if team=row.teamB then some (some Role.receiveB) else some none) else none) = _
      simp [ha,hb]
    rw [Range.teamCost,hs,Range.incident,ite_eq_right h]
    split <;> first | rfl | split <;> rfl

/-- The concrete bound used when inserting the transmission fragment into the team clock.
It is linear in the number of public records plus the incident bit width at this team. -/
theorem directory_tick_bound (rows : ℕ → Range w) (team : Word w) (count : ℕ) :
    setup.slots + (20+decision.depth)*count +
      (∑ i ∈ Finset.range count, (rows i).teamCost team) + 1 ≤
      256*(1+count+∑ i ∈ Finset.range count, (rows i).incident team) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range count) => (rows i).teamCost_le team)
  rw [← Finset.mul_sum] at h
  have hs : setup.slots + 1 ≤ 256 := by decide
  have hd : 20+decision.depth ≤ 256 := by decide
  have ht := Nat.mul_le_mul_right count hd
  omega

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI

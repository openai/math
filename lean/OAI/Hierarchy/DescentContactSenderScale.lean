import OAI.Hierarchy.DescentContactCostUnit
import OAI.Hierarchy.DescentContactSenderPrice

namespace OAI
/-! # Local coefficients for the four original sender scans -/
namespace Hierarchy.DescentContactSenderDate.Layout
open DescentSIMDLookup DescentContactCostUnit
variable {D L cap n r Ht b : ℕ} (A : Layout D L cap n r Ht b)

def scanClock (N F S jobs D U : ℕ) :=
  clock N 1 (gatherLimit N U)+(4+10*(F*3))+clock 2 F (gatherLimit 2 7)+
    clock S jobs (gatherLimit S (returnLimit D U))+clock S jobs (gatherLimit S (returnLimit D U))

def scanNames (N F S jobs D U : ℕ) :=
  names N 1 (gatherLimit N U)+15*(F*3+1)+names 2 F (gatherLimit 2 7)+
    names S jobs (gatherLimit S (returnLimit D U))+names S jobs (gatherLimit S (returnLimit D U))

local notation "N" => DescentOldContactSender.count D L cap n r
local notation "F" => DescentOldContactSender.lanes L cap
local notation "P" => b*F
local notation "jobs" => (L*(2*cap))*2
local notation "S" => DescentResetOppositePayload.span D cap

theorem scan_scale (U h T : ℕ) (rows : A.hosts*chunks A.groups A.batch≤T) (lut : 2^(h/2)≤T)
    (board : (b*N+b)*A.batch≤h/2) (split : (P*2+P)*A.batch≤h/2)
    (returns : (b*S+b)*A.batch≤h/2) :
    A.clockBound U≤ scanClock N F S jobs D U*T ∧ A.nameBound U≤ scanNames N F S jobs D U*T := by
  have pos : 0<T := (Nat.two_pow_pos _).trans_le lut
  have rc : A.localShape.rows≤1*T:=by simpa [DescentResetCandidateDate.Shape.rows,localShape] using rows
  have idx : A.indexSize≤(F*3)*T := left F (by simpa [DescentResetCandidateDate.Shape.stride,
    DescentResetCandidateDate.Shape.rowBits] using DescentContactCostUnit.span rc pos)
  obtain ⟨c₁,n₁⟩:=scan A.localShape N b (gatherLimit N U) h T rows lut board
  obtain ⟨c₂,n₂⟩:=scan A.splitShape 2 P (gatherLimit 2 7) h T rows lut split
  obtain ⟨c₃,n₃⟩:=scan A.leftShape S b (gatherLimit S (returnLimit D U)) h T rows lut returns
  obtain ⟨c₄,n₄⟩:=scan A.rightShape S b (gatherLimit S (returnLimit D U)) h T rows lut returns
  exact ⟨sum (sum (sum (sum c₁ (sum (fixed 4 pos) (left 10 idx))) c₂) c₃) c₄,
    sum (sum (sum (sum n₁ (left 15 (sum idx (fixed 1 pos)))) n₂) n₃) n₄⟩

end Hierarchy.DescentContactSenderDate.Layout

end OAI

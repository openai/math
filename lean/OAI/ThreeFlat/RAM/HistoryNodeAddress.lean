import OAI.ThreeFlat.Diagonal.TickScratchRegion
import Mathlib.Tactic.Linarith

namespace OAI
/-! # Physical S12 addresses shared by the seed and assembled node caches -/

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal.TickWorkspace

def volume (u : ℕ) := 2^(u^10)

/-- Physical S12 offsets for the actual chronological ID. Leaf streams occupy
the first two sectors, assembled node streams occupy sectors 160 and 161. -/
def streamAt (u seedCount i : ℕ) :=
  base u 12+i*(volume u)^2+(if i<seedCount then 0 else 160)*(volume u)
def endsAt (u seedCount i : ℕ) := streamAt u seedCount i+volume u

theorem address_limits {u seedCount i rows ext : ℕ} (large : 162≤volume u)
    (cells : 4*rows≤volume u) (pins : ext≤volume u) :
    base u 12+i*(volume u)^2≤streamAt u seedCount i ∧
    streamAt u seedCount i+4*rows≤endsAt u seedCount i ∧
    endsAt u seedCount i+ext≤base u 12+(i+1)*(volume u)^2 := by
  have offset : (if i<seedCount then 0 else 160)≤160 := by split <;> decide
  have offsetBound:=Nat.mul_le_mul_right (volume u) offset
  have blockRoom:=Nat.mul_le_mul_right (volume u) large
  unfold endsAt streamAt
  exact ⟨Nat.le_add_right ..,by omega,by nlinarith only [offsetBound,blockRoom,pins]⟩

end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI

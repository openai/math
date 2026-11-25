import OAI.Hierarchy.TraceReceiverGridWindow
import OAI.Hierarchy.TraceReceiverTaskReads

namespace OAI
/-! # Bounds for preparing selected-root tables in the actual receiver banks -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat Diagonal RAM
open TraceAdmission
open scoped Classical

/-- The width scans use scratch above their output prefixes. All three
prefixes are disjoint from the five-word task table they subsequently feed. -/
theorem grid_before_room {w n : ℕ} (large : 7≤w) (age : (receiverAge w)^10≤5*w)
    (count : 5*n≤GridReceiverBanks.gap w) (selection : n≤TickWorkspace.stride (receiverAge w)) :
    BeforeBounds (GridReceiverBanks.tasks w) (TickWorkspace.base (receiverAge w) 18+1)
      (GridReceiverBanks.limit w) (GridReceiverBanks.width w) n (64*w) := by
  obtain ⟨bank,roof,slots⟩ := TraceFactorReceiver.Gather.grid_window large age
  let age' := receiverAge w
  have low11 := TickWorkspace.apart (u:=age') (by decide : 11<45)
  have low17 := TickWorkspace.apart (u:=age') (by decide : 17<45)
  have low18 := TickWorkspace.apart (u:=age') (by decide : 18<45)
  have pos : 0<TickWorkspace.stride age' := by unfold TickWorkspace.stride;positivity
  change TickWorkspace.base age' 45 < GridReceiverBanks.base w at bank
  change n≤TickWorkspace.stride age' at selection
  constructor
  · change GridReceiverBanks.base w+7 < _;omega
  · change TickWorkspace.base age' 18+1 < GridReceiverBanks.base w;omega
  · change TickWorkspace.base age' 11+3*(TickWorkspace.stride age'/4) < GridReceiverBanks.base w;omega
  · change TickWorkspace.base age' 17+n ≤ GridReceiverBanks.base w;omega
  · change GridReceiverBanks.base w+7 ≤ GridReceiverBanks.base w+_;omega
  · change GridReceiverBanks.base w+GridReceiverBanks.gap w+5*n < _;omega
  · intro j
    fin_cases j <;> constructor <;>
      simp [prefixLayout,GridReceiverBanks.tasks,GridReceiverBanks.limit,GridReceiverBanks.width,columnBase] <;> omega
  · intro j
    fin_cases j <;> simp [GridReceiverBanks.tasks,GridReceiverBanks.width] <;> omega
  · intro j
    fin_cases j <;> simp [GridReceiverBanks.tasks,columnBase] <;> omega
  · intro j i hi
    apply Or.inr
    fin_cases j <;> simp [GridReceiverBanks.tasks,columnBase,GridReceiverBanks.width] <;> omega
  · intro j
    fin_cases j <;> constructor <;>
      simp [GridReceiverBanks.tasks,columnBase] <;> omega

/-- Different selected amounts are separated by a full sector-30 gap. -/
theorem grid_column_separation {w n : ℕ} (_large : 7≤w) (count : 5*n≤GridReceiverBanks.gap w) :
    ColumnSeparation (GridReceiverBanks.tasks w) (GridReceiverBanks.width w) n := by
  have positive : 0<GridReceiverBanks.gap w := by unfold GridReceiverBanks.gap; positivity
  constructor
  · intro j k
    fin_cases j <;> fin_cases k <;> simp [columnBase,GridReceiverBanks.tasks,GridReceiverBanks.width] <;> omega
  · intro j k distinct
    fin_cases j <;> fin_cases k <;> simp_all [columnBase,GridReceiverBanks.tasks] <;> omega

/-- Apply the terminal site bound from the registered physical compression
run directly to the selected subset of that same tick. -/
theorem grid_before_sites {w n : ℕ} (large : 7≤w) (age : (receiverAge w)^10≤5*w)
    (sites : n≤2^(3*w/5)) :
    BeforeBounds (GridReceiverBanks.tasks w) (TickWorkspace.base (receiverAge w) 18+1)
      (GridReceiverBanks.limit w) (GridReceiverBanks.width w) n (64*w) ∧
    ColumnSeparation (GridReceiverBanks.tasks w) (GridReceiverBanks.width w) n := by
  have nfit : 5*n≤GridReceiverBanks.gap w := calc
    5*n ≤ 2^3*2^(3*w/5) := Nat.mul_le_mul (by decide) sites
    _ = 2^(3+3*w/5) := (pow_add ..).symm
    _ ≤ GridReceiverBanks.gap w := Nat.pow_le_pow_right (by decide) (by omega : 3+3*w/5≤4*w)
  have sfit : n≤TickWorkspace.stride (receiverAge w) := calc
    _ ≤ 2^(3*w/5) := sites
    _ ≤ 2^((receiverAge w)^10*4) := Nat.pow_le_pow_right (by decide) (by have := receiverAge_lower w;omega)
    _ = _ := pow_mul ..
  exact ⟨grid_before_room large age nfit sfit,grid_column_separation large nfit⟩

/-- The four metadata words which the native parent writer mounted immediately
before the scans survive all three prefixes and all five-word task writes. -/
theorem before_parent_frame {w n : ℕ} (large : 7≤w) (m : Computability.VPVNP.BurstRAM.Memory (64*w))
    (j : Fin 4) (count : ℕ) :
    let D:=GridReceiverBanks.tasks w
    beforeImage D count (GridReceiverBanks.limit w) (GridReceiverBanks.width w)
      n m (D.parent+j.val)=m (D.parent+j.val) := by
  intro D
  have room : 128≤GridReceiverBanks.gap w :=
    Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 7≤4*w)
  have hj:=j.isLt
  apply before_away
  · apply Or.inr
    change GridReceiverBanks.base w+7≤GridReceiverBanks.base w+16+j.val;omega
  · apply Or.inl
    change GridReceiverBanks.base w+16+j.val<GridReceiverBanks.base w+GridReceiverBanks.gap w;omega
  · intro k;apply Or.inl
    fin_cases k <;> simp [D,GridReceiverBanks.tasks,GridReceiverBanks.width] <;> omega
  · intro k;apply Or.inl
    fin_cases k <;> simp [D,GridReceiverBanks.tasks,columnBase] <;> omega

end Hierarchy.TraceReceiverTasks

end OAI

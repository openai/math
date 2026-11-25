import OAI.Hierarchy.ProtocolRAMCalendarCatalystArchive
import OAI.Hierarchy.ProtocolRAMPurchaseFrozenCount
import OAI.Hierarchy.ProtocolRAMCalendarLinearRoom

namespace OAI
/-! # Space and time of the paid reserve archive at the physical market size -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar ProbeStage ProbeStage.Native ProbeStage.CoreBoard
open scoped BigOperators Classical
variable {count payload : ℕ}

def recordFactor (c : Mesh) (d k degree depth ports : ℕ) :=
  fuel c*((2*rounds d+1)*(2*k))*degree^depth*ports

def resourceFactor (d k : ℕ) := (2+2*(18*(d-1)+1)*4^(rounds d+1))*k

/-- Each resource index is a genuine exposed physical column and catalyst
axis. At fixed radix its cardinality grows linearly in the number of wires. -/
theorem physical_resources (z d k : ℕ) (radix : 1≤d) :
    Fintype.card (Columns z d)*k ≤ resourceFactor d k*2^z := by
  have cells := reserve_total_bound (h:=z) (k:=k) (w:=1) (R:=1) (B:=1) radix (by decide)
  rw [reserve_count] at cells
  have height : Stages z d=18*(d-1)+1 := by
    change (template (ProbeStage.radix z d) (radix_pos z d) (rounds d) Unit (2^z)).shapes.length = _
    rw [template_length]
    unfold rounds
    omega
  simpa only [height,Nat.mul_one,resourceFactor] using cells

/-- Finite price strata and finite path depth precede the permutation size.
Every row in both the payload and purchase rectangles, including dormant
rows, is charged at the true common role stride. -/
theorem market_records (c : Mesh) (issued : Attempt→Entry count payload)
    (z d k degree depth ports : ℕ)
    (capacity : ∀a,(issued a).rows≤PurchaseFrozen.count z d k*PurchaseFrozen.paths z degree depth*ports) :
    recordCount c issued ≤ recordFactor c d k degree depth ports*2^z := by
  let block := PurchaseFrozen.count z d k*PurchaseFrozen.paths z degree depth*ports
  have each (t : Fin (events c).length) : (atTime c issued t).rows≤block := by
    unfold atTime
    cases (events c).get t with
    | feed _ => exact Nat.zero_le _
    | attempt a => exact capacity a
  calc
    _ ≤ ∑ _t : Fin (events c).length,block := Finset.sum_le_sum (fun t _=>each t)
    _ = (events c).length*block := by simp
    _ = _ := by rw [event_count]; dsimp [block,recordFactor,fuel,PurchaseFrozen.paths]
                rw [PurchaseFrozen.count_eq];ring

/-- Concrete number of words required for two public lookups per row and
the full native reserve scatter. -/
theorem archive_clock (c : Mesh) (issued : Attempt→Entry count payload)
    (a : ReserveUse.Archive) (b : RouteSettlement.Banks) (reserve z d k degree depth ports C : ℕ)
    (resources : count ≤ C*2^z)
    (capacity : ∀t,(issued t).rows≤PurchaseFrozen.count z d k*PurchaseFrozen.paths z degree depth*ports) :
    ReserveUse.clock a b count (recordCount c issued) reserve ≤
      (19+12*C+160*recordFactor c d k degree depth ports)*2^z := by
  have rows := market_records c issued z d k degree depth ports capacity
  have base : 19≤19*2^z := by simpa using Nat.mul_le_mul_left 19 (Nat.two_pow_pos z)
  rw [ReserveUse.clock_eq]
  calc
    _ ≤ 19*2^z+12*(C*2^z)+160*(recordFactor c d k degree depth ports*2^z) := by omega
    _ = _ := by ring

theorem pointer_room (c : Mesh) (issued : Attempt→Entry count payload) (z d k degree depth ports C : ℕ)
    (capacity : ∀t,(issued t).rows≤PurchaseFrozen.count z d k*PurchaseFrozen.paths z degree depth*ports)
    (large : C+2*recordFactor c d k degree depth ports≤z) :
    C*2^z+2*recordCount c issued < 2^(wordBits z d copies) := by
  have rows := market_records c issued z d k degree depth ports capacity
  calc
    _ ≤ C*2^z+2*(recordFactor c d k degree depth ports*2^z) := Nat.add_le_add_left (Nat.mul_le_mul_left 2 rows) _
    _ = 2^z*(C+2*recordFactor c d k degree depth ports) := by ring
    _ < _ := Calendar.GlobalTests.linear_room z d _ large

/-- On the true column layout there is no external assumption controlling
the number of reserve accounts. -/
theorem physical_clock (c : Mesh) (z d k degree depth ports : ℕ) (radix : 1≤d)
    (issued : Attempt→Entry (Fintype.card (Columns z d)*k) payload)
    (a : ReserveUse.Archive) (b : RouteSettlement.Banks) (reserve : ℕ)
    (capacity : ∀t,(issued t).rows≤PurchaseFrozen.count z d k*PurchaseFrozen.paths z degree depth*ports) :
    ReserveUse.clock a b (Fintype.card (Columns z d)*k) (recordCount c issued) reserve ≤
      (19+12*resourceFactor d k+160*recordFactor c d k degree depth ports)*2^z :=
  archive_clock c issued a b reserve z d k degree depth ports _ (physical_resources z d k radix) capacity

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI

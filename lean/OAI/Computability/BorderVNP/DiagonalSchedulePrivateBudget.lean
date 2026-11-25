import OAI.Computability.BorderVNP.DiagonalScheduleMachineBudget
import OAI.Computability.BorderVNP.RoutingISATypedPrivateClock

/-! # The complete private cell evaluation within the common machine window

The input contains the original table directory and exterior assignment. Its
measured native execution fits the two physical limits and sums to the true
cell weight. The same choice of batch exponent admits the field installations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter TeamScales CellSparse RoutingISA CompactMachine
open scoped BigOperators
universe u

/-- The complete finite typed cell driver at this batch and processor length,
from original-format and scalar-width bounds on the supplied directory. -/
def PrivateCellBudgetAt (A T B j H R k n r : ℕ) : Prop :=
  ∀ M E w U : ℕ, M ≤ width n (1/5) → E ≤ width n (1/4) → 0 < w → w ≤ n →
    ∀ c : CellInput, c.external.length ≤ E → c.directory.StaticBounds A M →
    c.directory.CompactFields c.privateWires (4*(M+E+1)^3) →
    c.directory.records.length ≤ 4*(M+E+1)^3 → c.directory.reportedCounts.length ≤ 4*(M+E+1)^3 →
    Packet.storedMass c.directory ≤ A*(M+1)^2 → Packet.RawFields c.directory c.privateWires U →
    U.size+1 ≤ B*(logWidth r n+1)^j → (∀ rec ∈ c.directory.records, (Packet.record rec).length ≤ H) →
    (∀ fs ∈ c.directory.boxes, ∀ f ∈ fs, f.TableBound T) →
    (∀ bs ∈ c.directory.reportedCounts, bs.length ≤ R*(logWidth r n+1)^k) → c.directory.ProfileWidths →
    (CompactFrame.pack w (Packet.input c.directory c.privateWires c.external)).length ≤ width n (1/2) ∧
    TypedBatch.cellClock w c ≤ n^25 ∧
      ∑ o ∈ choices TypedBatch.cellDriver n (CompactFrame.pack w (Packet.input c.directory c.privateWires c.external)),
        o.2.value = c.weight

/-- Choose the batch exponent once for all four machine bounds and the real
signed private cell contraction. Only the fixed input-format constants precede it. -/
theorem exists_machineBudget_with_private {α τ : ℝ} (hα : 0 < α) (ha : α < 1/1000) (hτ : 0 < τ)
    (ht : τ < α/100) (E d A T B j H R k : ℕ) :
    ∃ ω : ℝ, 0 < ω ∧ MachineBudget.{u} α τ E d A B j ω ∧
      AdmissibleRange ω (PrivateCellBudgetAt A T B j H R k) := by
  obtain ⟨v,hv,machine⟩ := exists_machineBudget.{u} hα ha hτ ht E d A B j
  obtain ⟨w,hw,privateCell⟩ := TypedBatch.eventually_private_cell A T B j H R k
  have cell : AdmissibleRange w (PrivateCellBudgetAt A T B j H R k) := by
    filter_upwards [privateCell] with n check
    intro r hr room M E' word U hm he hword hlen
    exact check r M E' word U hr room hm he hword hlen
  exact ⟨min v w,lt_min hv hw,machine.shrink (min_le_left ..),cell.shrink (min_le_right ..)⟩

end Diagonal

end BorderVNP
end Computability
end OAI

import OAI.Hierarchy.TraceDistribution
import OAI.Hierarchy.PhysicalTracePlan
import OAI.ThreeFlat.Diagonal.PhysicalBlockTreeSize

namespace OAI
/-! # Counts of external pins reaching a specific physical terminal site -/

noncomputable section
namespace Hierarchy.TraceDistribution

open ThreeFlat LinearAlgebra.SpectralBooks
open Diagonal Diagonal.HistoryContraction Diagonal.LaneCursor
open scoped BigOperators Classical

variable {F : Type} [Field F]

namespace Physical

variable (B : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1) (low offsets slots : ℕ)

private theorem ancestors_after_recast (B : PhysicalStage.Block F) {lanes : ℕ}
    (enough : 2≤lanes) (s rem low offsets slots : ℕ) (e : lanes=(B.repeat s).charge+rem) :
    let A := B.cursorState enough low offsets slots
    let r := PhysicalStage.Program.recast e A ((B.repeat s).run rem (e ▸ A))
    ∀ (h : r.plan.History) (v : (r.plan.finish h).Site),
      Nat.card {i // r.plan.destination h i=v} ≤ 2^(B.blockCharge*s) := by
  subst lanes
  exact B.oldest_positions_le s rem (B.cursorState enough low offsets slots)

theorem ancestors (s low offsets slots : ℕ) (fits : B.blockCharge*s ≤ k+1) :
    let Q := (run B hk low offsets slots s fits).plan
    ∀ (h : Q.History) (v : (Q.finish h).Site),
      Nat.card {i // Q.destination h i=v} ≤ 2^(B.blockCharge*s) := by
  have e : k+1=(B.repeat s).charge+(k+1-(B.repeat s).charge) := by rw [B.charge_repeat]; omega
  exact ancestors_after_recast B hk s (k+1-(B.repeat s).charge) low offsets slots e

section Native

variable {low : ℕ}

open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory

variable [Fintype F] {w pc regs words S base fuel : ℕ}
variable (M : Machine w pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^w) (st : Word w)

/-- With each bucket restricted to its external prefix, the concrete native
factor sees at most two row-sized blocks of pins per ancestral position. -/
theorem repeated_native_pins (s : ℕ) (fits : B.blockCharge*s ≤ k+1) {prefixSize : ℕ} (extent : prefixSize≤S) :
    let Q := (nativeRun B hk M t hF st s fits).plan
    ∀ (h : Q.History) (v : (Q.finish h).Site),
      Nat.card {j : Fin prefixSize // Q.destination h
        (PairedCursor.owner (layout M t hF st) ⟨j.val,j.isLt.trans_le extent⟩)=v} ≤
        2^(B.blockCharge*s)*(2*2^low) := by
  intro Q h v
  exact (native_factor_pins M t hF st extent (Q.destination h) v).trans
    (Nat.mul_le_mul_right _ (ancestors B hk s low _ _ fits h v))

end Native

end Physical


end Hierarchy.TraceDistribution

end
end OAI

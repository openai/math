import OAI.Computability.BorderVNP.RoutingISATableIntervalKernel
import OAI.Computability.BorderVNP.RoutingISATableClear

/-! # Linear-time native compilation of every transmission interval -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Clearing just the square table establishes the initial width and ordinal invariant. -/
theorem intervalImage_cleared (l : TableLayout) (row : ℕ → TableRow) (m : ℕ → ℕ) :
    l.IntervalImage row m 0 (zeroPrefix l.widths (l.teams^2) m) := by
  constructor
  · intro k hk
    simp [zeroPrefix, TableLayout.pairWidth, hk]
  · intro i hi
    omega
  · intro x hx _
    change ¬ (l.widths ≤ x ∧ x < l.widths+l.teams^2) at hx
    simp [zeroPrefix, hx]

/-- The fixed interval pass visits one whole seven-word descriptor per iteration.
The terminal square table and every interval ordinal are certified against the mathematical
prefix counts, including records with zero width and co-located endpoints. -/
theorem run_intervalPass {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : TableLayout) (row : ℕ → TableRow) (al : l.Allocated w) (fit : l.RowsFit w row)
    (before : ℕ → ℕ) (initial : l.recordsMatch row before)
    (s : Bank w) (m : Memory w) (ready : l.ready (.ofWords s m))
    (start : l.IntervalImage row before 0 (readings m)) :
    BoundedRun pub macros intervalPass s m (l.count*(tabulateInterval.slots+1)+2)
      (fun z => l.ready z ∧ l.IntervalImage row before l.count z.mem) := by
  let P (i : ℕ) (z : NatState) := l.ready z ∧ z.reg 13 = i ∧ l.IntervalImage row before i z.mem
  have regs (i : ℕ) (z : NatState) (h : P i z) : z.reg 13 = i ∧ z.reg 7 = l.count :=
    ⟨h.2.1, h.1 7 (by decide)⟩
  have step (i : ℕ) (hi : i < l.count) (u : Bank w) (mu : Memory w)
      (h : P i (.ofWords u mu)) : BoundedRun pub macros tabulateInterval u mu tabulateInterval.slots (P (i+1)) :=
    (run_tabulateInterval pub macros l row al fit before initial i hi u mu h.1 h.2.1 h.2.2).mono le_rfl
      (fun _ hz => ⟨hz.1,hz.2.1,hz.2.2 ▸ h.2.2.store al fit hi⟩)
  have init := (Code.copy 13 0).runFixed pub macros s m trivial
  have run := init.seq (b := .whileLt 13 7 tabulateInterval)
    (t := (l.count-0)*(tabulateInterval.slots+1)+1) (Q := P l.count)
    (fun u mu hu => run_counted_loop pub macros 13 7 tabulateInterval l.count tabulateInterval.slots
      P regs step 0 (Nat.zero_le _) u mu (by
        rw [hu]
        refine ⟨TableLayout.ready_fixed ready (c := .copy 13 0) (by decide) _, ?_, start⟩
        simp [Code.fixedEval,Code.evalNat, show (NatState.ofWords s m).reg 0 = 0 from ready 0 (by decide)]))
  exact run.mono (by change 1+((l.count-0)*(tabulateInterval.slots+1)+1) ≤ _; rw [Nat.sub_zero]; omega)
    fun _ h => ⟨h.1,h.2.2⟩

end RoutingISA

end BorderVNP
end Computability
end OAI

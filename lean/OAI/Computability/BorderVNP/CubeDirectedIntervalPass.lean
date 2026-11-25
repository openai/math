import OAI.Computability.BorderVNP.CubeDirectedIntervalKernel

/-! # Native scan of all processed cable descriptors in their public row order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Scan only cable rows, independently of their widths. -/
def cablePass : Code := .block [.copy 13 0,.whileLt 13 4 cableStep]

/-- The native pass consumes one fixed block per input descriptor and leaves the
entire directed width and ordinal image in RAM. It accepts empty directories. -/
theorem run_cablePass {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) (s : Bank w) (m : Memory w)
    (ready : l.Ready (.ofWords s m)) (image : l.Image before 0 (readings m)) :
    BoundedRun pub macros cablePass s m (2+l.count*(cableStep.slots+1))
      (fun z => l.Ready z ∧ l.Image before l.count z.mem) := by
  let P (i : ℕ) (z : NatState) := l.Ready z ∧ z.reg 13 = i ∧ l.Image before i z.mem
  have regs (i : ℕ) (z : NatState) (hz : P i z) : z.reg 13 = i ∧ z.reg 4 = l.count :=
    ⟨hz.2.1,hz.1 4 (by decide)⟩
  have step (i : ℕ) (hi : i < l.count) (s : Bank w) (m : Memory w) (hz : P i (.ofWords s m)) :
      BoundedRun pub macros cableStep s m cableStep.slots (P (i+1)) :=
    run_cableStep pub macros l before fit hi s m hz.1 hz.2.1 hz.2.2
  have init := (Code.copy 13 0).runFixed pub macros s m trivial
  have run := init.seq (b := .whileLt 13 4 cableStep) (t := (l.count-0)*(cableStep.slots+1)+1) (Q := P l.count)
    (fun u mu hu => run_counted_loop pub macros 13 4 cableStep l.count cableStep.slots P regs step
      0 (Nat.zero_le _) u mu (by
        rw [hu]
        exact ⟨ready.fixed (c := .copy 13 0) (by decide) _,ready 0 (by decide),image⟩))
  exact run.mono (by change 1+((l.count-0)*(cableStep.slots+1)+1) ≤ _; rw [Nat.sub_zero]; omega) fun _ h => ⟨h.1,h.2.2⟩

/-- The cleared square array is the image of the empty prefix, with arbitrary previous memory. -/
theorem cleared_image (l : Layout) (before : ℕ → ℕ) :
    l.Image before 0 (zeroPrefix l.widths (l.alphabet^2) before) := by
  constructor
  · intro k hk
    simp [zeroPrefix,Layout.prefix,hk]
  · intro i hi
    omega
  · intro x hx _
    simp [zeroPrefix,hx]

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI

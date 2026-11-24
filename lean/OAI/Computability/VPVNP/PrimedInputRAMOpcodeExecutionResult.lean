import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecutionLayout

/-!
# The physical input assembler for the two primed groups

The fixed opcode table, started in the prescribed header memory, has one
accepting native path per internal bit assignment. Every parser leaf receives
the corresponding tape bit. Three cut-length reads on each of the two visits
to a rectangular position increase the total cost by exactly six per position.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Layout

open BurstRAM Opcodes

variable {L : Lengths} {n r H w : ℕ} (Q : Layout L n r H w)

/-- The exact cost is the scheduled cost plus three length reads at each data
call. The same uniform upper bound applies to every assignment and memory. -/
theorem native_cost_bound (m : Memory w) :
    scheduledCost (nativeOps Q) + 3 * (positions n r + positions n r) ≤
      11 * positions n r + 1 := by
  have h := (Q.twoPass (encodeBit w)).scheduledCost_le (encodeBit w) Q.cursorFits m
  change scheduledCost (nativeOps Q) ≤ 5 * positions n r + 1 at h
  omega

/-- Histories of the actual fixed opcode machine enumerate the shared internal
bits in the two primed groups. The auxiliary RAM's caps include its header reads. -/
def nativePathEquiv (F : ParameterFit Q) (m : Memory w) (hc : CutMemory L m) {S K : ℕ}
    (hK : 6 ≤ K) (hTotal : 11 * positions n r + 1 ≤ S * K) :
    ActualPaths (nativeMachine Q).program (nativeFuel r) 0 m (withinCaps S K) ≃
      (Internal L r H w → Bool) :=
  ((physicalSchedule Q F).pathEquiv m hc hK ((Q.native_cost_bound m).trans hTotal)).trans
    (Q.inputPathEquiv (encodeBit w) m (by omega) (by omega))

/-- The opcode report list and the semantic input-pass reports carry the same
memory updates and cursor returns, with three additional probes per data call. -/
theorem nativeRun_matches (F : ParameterFit Q) (m : Memory w) (hc : CutMemory L m) {S K : ℕ}
    (hK : 6 ≤ K) (hTotal : 11 * positions n r + 1 ≤ S * K)
    (p : ActualPaths (nativeMachine Q).program (nativeFuel r) 0 m (withinCaps S K))
    {rs : List (Report w)} (hr : runSegment (nativeMachine Q).program (nativeFuel r) (some 0) m p.val =
      some rs) : MatchedReports m rs (Q.inputReports (encodeBit w) (Q.nativePathEquiv F m hc hK hTotal p) m) := by
  let path := (physicalSchedule Q F).pathEquiv m hc hK ((Q.native_cost_bound m).trans hTotal) p
  have hg := Q.run_inputPath (encodeBit w) m (by omega : 3 ≤ K)
    (by omega : 5 * positions n r + 1 ≤ S * K) path
  have hs := (physicalSchedule Q F).run_matched 0 (Nat.zero_le _) m hc p.val
  change Option.Rel _ (runSegment (nativeMachine Q).program (nativeFuel r) (some 0) m p.val)
    (runSegment (Q.inputProgram (encodeBit w)) 3 (some 0) m path.val) at hs
  rw [hr, hg, Option.rel_some_some] at hs
  exact hs

theorem nativeRun_memory (F : ParameterFit Q) (m : Memory w) (hc : CutMemory L m) {S K : ℕ}
    (hK : 6 ≤ K) (hTotal : 11 * positions n r + 1 ≤ S * K)
    (p : ActualPaths (nativeMachine Q).program (nativeFuel r) 0 m (withinCaps S K))
    {rs : List (Report w)} (hr : runSegment (nativeMachine Q).program (nativeFuel r) (some 0) m p.val =
      some rs) : after m (eventLog rs) = Q.assembled (encodeBit w) (Q.nativePathEquiv F m hc hK hTotal p) m :=
  (Q.nativeRun_matches F m hc hK hTotal p hr).after_eq.trans (Q.after_inputReports ..)

/-- Every address below the scratch rectangle is preserved, including histogram
entries reserved there and all three cut-length words. -/
theorem nativeRun_preserves_header (F : ParameterFit Q) (m : Memory w) (hc : CutMemory L m) {S K : ℕ}
    (hK : 6 ≤ K) (hTotal : 11 * positions n r + 1 ≤ S * K)
    (p : ActualPaths (nativeMachine Q).program (nativeFuel r) 0 m (withinCaps S K))
    {rs : List (Report w)} (hr : runSegment (nativeMachine Q).program (nativeFuel r) (some 0) m p.val =
      some rs) {a : ℕ} (ha : a < Q.scratchBase) : after m (eventLog rs) a = m a := by
  rw [(Q.nativeRun_matches F m hc hK hTotal p hr).after_eq]
  exact Q.inputReports_preserve_header _ _ _ ha

/-- Every actual opcode run writes the selected internal assignment's exact
primed input bit at each physical site and tape offset. -/
theorem nativeRun_input (F : ParameterFit Q) (hdr : Header L → Bool) (hist : List (Word w)) {S K : ℕ}
    (hK : 6 ≤ K) (hTotal : 11 * positions n r + 1 ≤ S * K)
    (p : ActualPaths (nativeMachine Q).program (nativeFuel r) 0 (headerMemory L hdr hist) (withinCaps S K))
    {rs : List (Report w)} (hr : runSegment (nativeMachine Q).program (nativeFuel r) (some 0)
      (headerMemory L hdr hist) p.val = some rs) (u : Site r) (j : Fin n) :
    after (headerMemory L hdr hist) (eventLog rs) (Q.outputAddress (finProdFinEquiv (finProdFinEquiv u,j))).val =
      encodeBit w (input Q.program Q.fits hdr
        (Q.nativePathEquiv F _ (cutMemory_header Q hdr hist) hK hTotal p) u j) := by
  rw [Q.nativeRun_memory F _ (cutMemory_header Q hdr hist) hK hTotal p hr]
  exact Q.assembled_input _ _ _ _ (headerMemory_bits L hdr hist) u j

/-- Exact and uniform bounds for the native reports of any accepting opcode
history, without first imposing a cost cap on that history. -/
theorem nativeRun_cost (F : ParameterFit Q) (m : Memory w) (hc : CutMemory L m)
    (bits : List (List Bool)) {rs : List (Report w)}
    (hr : runSegment (nativeMachine Q).program (nativeFuel r) (some 0) m bits = some rs)
    (hend : endState (some 0) rs = none) :
    RAMBuckets.cost Report.probes rs = scheduledCost (nativeOps Q) + 6 * positions n r ∧
      RAMBuckets.cost Report.probes rs ≤ 11 * positions n r + 1 ∧ ∀ call ∈ rs, 1 + call.probes ≤ 6 := by
  obtain ⟨hs, hp⟩ := (physicalSchedule Q F).accepted_cost m hc bits hr hend
  have hbound := Q.native_cost_bound m
  change RAMBuckets.cost Report.probes rs = scheduledCost (nativeOps Q) +
    3 * (positions n r + positions n r) at hs
  exact ⟨by omega, hs.trans_le hbound, hp⟩

end PrimedInputRAM.Layout

end VPVNP
end Computability
end OAI

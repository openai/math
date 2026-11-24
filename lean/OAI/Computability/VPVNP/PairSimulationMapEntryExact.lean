import OAI.Computability.VPVNP.PairSimulationMapEntry
import OAI.Computability.VPVNP.PairSimulationMapSelectorClock
import OAI.Computability.VPVNP.PairSimulationMapFinishExact

/-!
# Successful grouped map calls have an exact clock and private state

The successful selector sequence fixes the tag checks, row dispatches and group
widths. The endpoint bits fix the label comparisons. The same deterministic
path writes the two staging arrays and increments exactly the emitted labels.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapEntry.Program

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord MotifSelector MotifEntry
open MotifBlocks MotifGrid MotifConversion MapPortAgreement MapResidentAgreement
open scoped Fin.CommRing

variable {K J D E : Type} [Field K] [Fintype J] [DecidableEq J] [Fintype D] [Fintype E]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {w p r k u t : ℕ} (P : Program B z j p r k)
  {demand : D → ℕ} {v : E → ℕ} {d : DemandBits src dst demand j}
  {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}

/-- Every successful call on the same input uses this tick count at all ready
configurations, including calls with different initial histogram counts. -/
noncomputable def successTicks (d : DemandBits src dst demand j)
    (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j) (θ : Fin u → Selector B)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (words : Fin k → BurstRAM.Word w) : ℕ :=
  P.selector.successTicks (selectorCode B) θ (ports G j P.edgeOrder).length +
    P.driverTicks d x θ fd fs words + ((Fintype.card E + 1) + (7 * u + 1))

set_option maxHeartbeats 1000000 in
-- The three native prefixes share dependent row, width, and private-memory operands.
/-- Execute the three linked phases. The successful prefix, tick bound, continuation,
persistent state, and equality of every private word refer to the same endpoint. -/
theorem native_success_exact (X : Workspace P demand v d x t w) (M : Machine w p r k)
    (linked : P.Linked M) (separate : P.Separate) (selector : Selector B ↪ BurstRAM.Word w)
    (ordinal : (parameterData B).Entry → Fin t) (fb : B.selectorBits ≤ w)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (pub : P.Public M selector (fun s ↦ ((ordinal s).val : BurstRAM.Word w)) fb fd fs)
    (c : Config w p r) (ready : P.Ready X c) (θ : Fin u → Selector B)
    (selected : (selectorRun G (selectorTable B) (selectorCode B) v j x).1 = some θ)
    (valid : ∀ e, v e = totalWidth (basePayload B) θ e) :
    let ticks := P.successTicks d x θ fd fs M.publicData
    ∃ out, ticks ≤ MapNativeClock.cap B z j u ∧ Prefix M c (List.replicate ticks .tick) out ∧
      out.pc = P.done ∧ out.persistent = c.persistent ∧
      out.privateMem = P.successMemory X selector ordinal θ c.privateMem := by
  classical
  dsimp only
  have hit : (selectorRun G P.selector.decoder.xs (selectorCode B) v j x).1 = some θ := by
    rw [linked.table]
    exact selected
  obtain ⟨m, first, frame, hm, sels⟩ := P.selector.native_success linked.selector P.edgeOrder
    fb (selectorCode B) pub.key x X.portBase X.directory X.source c ready.selector X.portsFit
    X.tagFit X.anchorFit X.ordinalFit X.anchorApart θ hit
  let labels := fun i ↦ ordinal (MapStream.readRow src dst (baseDemand B z) demand G
    (basePayload B) (lookup B z) v j d x i (θ i) (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i))
  obtain ⟨mid, h₂, rows, atWidth, totals, he, hist, labelWords, memory, hp⟩ :=
    P.runSelectedRows X M linked separate selector ordinal fb fd fs pub c ready θ m frame hm sels
  obtain ⟨out, last, done, bins, per⟩ := MapFinish.native_success (basePayload B) θ v
    (List.ofFn P.edgeOrder) _ P.expected P.guardTemp M P.guardPC P.histPC P.histReg P.done P.bad
    linked.guard linked.histogram X.target X.hist labels mid (atWidth.trans linked.rowExit)
    totals he hist X.histogramFit X.targetHistApart X.labelFit labelWords valid
  refine ⟨out, ?_, ?_, done, per.trans (hp.trans frame.persistent), ?_⟩
  · have h₁ := P.selector.successTicks_le (selectorCode B) θ (ports G j P.edgeOrder).length
    unfold AnchorDecode.Program.visitCap at h₁
    rw [linked.table] at h₁
    have hh := h₁.trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (ports_length_le G j P.edgeOrder)) _) _)
    change P.driverTicks d x θ fd fs M.publicData ≤
      (5 + 2 * (selectorTable B).length + MapRowLoop.rowCap B z j) * u + 1 at h₂
    unfold successTicks MapNativeClock.cap
    omega
  · unfold successTicks
    rw [List.replicate_add, List.replicate_add]
    simpa only [List.length_ofFn] using (first.append rows).append last
  · have sm : m.privateMem = PrivateScratch.write (X.source : BurstRAM.Word w)
        (fun i ↦ selector (θ i)) c.privateMem := by
      apply PrivateScratch.eq_write
      · intro i
        rw [← Nat.cast_add]
        exact (sels i).trans ((pub.name _).trans (pub.rows (.inl (θ i))))
      · intro a ha
        exact frame.memory a (PrivateScratch.outside_of_ne _ a ha)
    have lm : mid.privateMem = PrivateScratch.write (X.target : BurstRAM.Word w)
        (fun i ↦ ((labels i).val : BurstRAM.Word w)) m.privateMem := by
      apply PrivateScratch.eq_write
      · intro i
        simpa only [Nat.cast_add] using labelWords i
      · intro a ha
        exact memory a (PrivateScratch.outside_of_ne _ a ha)
    rw [bins, lm, sm]
    rfl

end PairSimulation.MapEntry.Program

end VPVNP
end Computability
end OAI

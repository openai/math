import OAI.Computability.VPVNP.LiveCompressedPairCursorStartup
import OAI.Computability.VPVNP.LiveCompressedPairStartupInputs
import OAI.Computability.VPVNP.LiveCompressedPairInitialTag

/-!
# Physical cursor startup at the paper's dimensions

The fixed compressed pair executes eight native calls on the actual eleven
public operands. One logarithmic private clock covers every call, uniformly
over the program prefix and incoming memory. The auxiliary shadow-copy stage
supplies the row counter's initial tag by `PreparedBranch.startup_tag`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM CursorBounds CompressorRecords CompressorRecords.Schedule
open scoped Fin.CommRing

variable {d initial phases : ℕ} {C : Catalog d}

/-- For the physical pair ABI, one logarithmic clock suffices at every large
input length. The incoming tag condition is the one established by the
preceding auxiliary preparation. -/
theorem eventually_physical_startup (c : Constants) (b : Bootstrap)
    (plan : Online.Config C initial phases) (terminal : PairTable) (B : ℕ) {H : ℕ → ℕ}
    (hB : 1 ≤ B) (hH : PolynomiallyBounded H) (hq : 0 < b.denominator) (hph : 0 < phases)
    (hθ : (b.numerator : ℝ)/b.denominator ≤ 1) (hlanes : b.lanesPerBlock ≤ B)
    (hArity : b.shape.arity = arity C) (arityFit : 7 ≤ b.shape.arity) (scalars : 30 ≤ b.shape.scalarFields) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ (lit : LiteralPrefix) (m : Memory (wordBits B n)) (cap : ℕ),
      let g := paperGeometry B H n
      let pub := Pieces.word g lit ∘ StageOperands.pair c
      let base := (Layout.pairWorkspace c).eval g
      m (PairTag.address pub).val = 0 → K*(n.log2+1) ≤ cap →
        StartupResult b plan terminal pub B n base m cap := by
  let D := bootstrapRows b initial phases
  let base n := (Layout.pairWorkspace c).eval (paperGeometry B H n)
  have hb : PolynomiallyBounded base := startup_workspace_polynomial c hB hH
  obtain ⟨K,clock⟩ := sourceFuel_log b initial phases 30
  refine ⟨K,?_⟩
  filter_upwards [eventually_startup_inputs c hB hH,
    TransferredStartup.eventually_run D d b.shape B b.degreeBits b.lanesPerBlock b.steps hB hq hph hθ
      hlanes arityFit scalars hb,
    DescriptorParameters.eventually_tight_end D b.shape B b.steps hB hb, Filter.eventually_ge_atTop 10]
    with n args start room size
  intro lit m cap g pub address initialTag large
  obtain ⟨hbase,len,width,tagBelow⟩ := args lit
  change (pub 6).val = n at len
  have hn : n < 2^wordBits B n := len.symm.trans_lt (pub 6).isLt
  have tagFit : 10 ≤ 2^wordBits B n := size.trans hn.le
  have lower : (PairTag.address pub).val < base n := lt_of_lt_of_eq tagBelow hbase
  have runs := start pub (PairTag.address pub) hbase len width lower m
  exact cursor_startup b plan terminal pub B n address m cap hArity tagFit (fun i ↦ (clock n i).trans large)
    initialTag runs hn scalars room

/-- A nonempty calendar runs its first online dispatch directly on the native
pair program, using the memory and tag left by the eight linked startup calls. -/
theorem StartupResult.first_online {w B n base cap : ℕ} {b : Bootstrap} {plan : Online.Config C initial phases}
    {terminal : PairTable} {pub : Fin 11 → Word w} {m : Memory w}
    (done : StartupResult b plan terminal pub B n base m cap)
    (positive : 0 < (CalendarRows.rows (bootstrapRows b initial phases) n : Word w))
    (j : Fin (initial+phases)) (hj : j.val = 0) (fit : 10 ≤ 2^w)
    (onlineFit : Online.N d (initial+phases) ≤ 2^w) {innerCap : ℕ}
    (budget : 30+2*(initial+phases)+2*Online.N d (initial+phases)+5 ≤ innerCap) :
    let mem := after m (eventLog (cursorStartupLogs b pub B n base m initial phases d))
    let p := Workspace.ports (arity C) (pub 2)
    let online := Online.linked p (Online.calendarIndex d (initial+phases))
      (LevelCalendar.dispatchReport (Online.calendar plan) p.data mem (Online.phaseIndex plan j))
    let P := program b plan terminal pub
    execute P (innerCap+24+30) (P.start 0) mem [] = some (report pub Stage.online (Workspace.report (pub 2) mem online)) := by
  intro mem p online P
  have dispatch := OnlineWorkspace.first_dispatch plan pub 0 mem _ _ done.ready positive j hj onlineFit budget
  exact execute_stage b plan terminal pub Stage.online fit (innerCap+24) _ le_rfl 0 mem done.tagged [] _ dispatch

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI

import OAI.Hierarchy.DescentTerminalEmitter
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Instruction names in the terminal emitter and its immutable data installation -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentExteriorShelf
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open DescentStaticWordColumn (names names_scan names_seq)

private theorem service_names (w j r t e origin : ℕ) :
    names (service w j r t e origin) = 740 := by
  obtain ⟨hl, hr, hs⟩ := text_bound w j r t e origin
  rw [names, hl, hr, hs]

private theorem score_names (w out n bound : ℕ) (e : Expr) :
    names (SumScores.procedure w out n bound e) = 11 + 4 * (19 + e.work) := by
  simp only [names, SumScores.procedure, PhysicalInputPhases.writing, Term.labels_eq,
    SumScores.step_binds]; omega

private theorem prefix_names (w out n : ℕ) (op : DescentTerminalHeaderPrefixRAM.Op) (e : Expr) :
    names (DescentTerminalHeaderPrefixRAM.program w out n op e) =
      11 + 4 * DescentTerminalHeaderPrefixRAM.work op e := by
  simp only [names, DescentTerminalHeaderPrefixRAM.program, PhysicalInputPhases.writing,
    Term.labels_eq, DescentTerminalHeaderPrefixRAM.binds]; omega

private theorem dense_names (w n : ℕ) (L : DescentTerminalDenseHeaderRAM.Layout) :
    names (DescentTerminalDenseHeaderRAM.program w n L) = 480 := by
  norm_num only [DescentTerminalDenseHeaderRAM.program, names_seq, prefix_names, names_scan,
    DescentTerminalHeaderPrefixRAM.work, DescentTerminalDenseHeaderRAM.carryExpr,
    DescentTerminalDenseHeaderRAM.fmtExpr, DescentTerminalDenseHeaderRAM.sourceKey,
    DescentTerminalDenseHeaderRAM.offsetExpr, DescentTerminalDenseHeaderRAM.previous, Expr.work]

private theorem plane_names (w : ℕ) (S : DescentTerminalDataPlane.Shape)
    (L : DescentTerminalDataPlane.Layout) :
    names (DescentTerminalDataPlane.program (w := w) S L) = 1705 := by
  simp only [DescentTerminalDataPlane.program, flagged, DescentTerminalPublicWordRAM.program,
    DescentTerminalRawJoin.program, names_seq, service_names, score_names, names_scan,
    DescentTerminalPublicWordRAM.work, dense_names]; rfl

private theorem header_names (w : ℕ) (L : Header) : names (L.program w) = 806 := by
  have rowCost : (DescentTerminalHeaderScatter.stage
      (DescentTerminalScatterChip.put L.tapes L.output L.sink)
      (DescentTerminalScatterChip.datum L.tapes L.shift) L.tapes.lane).work = 191 := by
    norm_num only [DescentTerminalHeaderScatter.stage, DescentTerminalScatterChip.put,
      DescentTerminalHeaderScatter.bounded, DescentTerminalScatterChip.dest,
      DescentTerminalScatterChip.datum, DescentTerminalScatterChip.target,
      DescentTerminalScatterChip.source, DescentTerminalScatterChip.live,
      DescentTerminalScatterChip.chunk, DescentTerminalScatterChip.group,
      DescentTerminalScatterChip.event, Expr.work]
  have scatter : names (EffectSeed.scatter w L.src L.events) = 16 := rfl
  norm_num only [Header.program, DescentTerminalScatterChip.boundedProgram,
    DescentTerminalHeaderScatter.program, names_seq, names_scan, rowCost, scatter, Expr.work]

private theorem gather_names (w n : ℕ) (L : DescentTerminalLocalPortBook.Gather) :
    names (L.program w n) = 243 := by
  norm_num only [DescentTerminalLocalPortBook.Gather.program, names_scan,
    DescentTerminalLocalPortBook.Gather.load, DescentTerminalLocalPortBook.Gather.raw, Expr.work]

private theorem route_names (w n : ℕ) (L : DescentTerminalRouteIssue.Layout) :
    names (DescentTerminalRouteIssue.program L w n) = 218 := by
  norm_num only [DescentTerminalRouteIssue.program, names_seq, prefix_names, names_scan,
    DescentTerminalHeaderPrefixRAM.work, DescentTerminalRouteIssue.row,
    DescentTerminalRouteIssue.project, Expr.work]

private theorem leaf_names (w src pool n out : ℕ) (L : DescentTerminalLeafFold.Layout) :
    names (DescentTerminalLeafFold.program w src pool n out L) = 331 := by
  have scatter : names (ProtocolRAMWeightedScatter.program w src n) = 22 := rfl
  norm_num only [DescentTerminalLeafFold.program, names_seq, names_scan, scatter,
    DescentTerminalLeafFold.row, DescentTerminalHeaderScatter.stage, DescentTerminalLeafFold.low,
    DescentTerminalHeaderScatter.bounded, DescentTerminalLeafFold.address,
    DescentTerminalLeafFold.high, DescentTerminalLeafFold.lookup, Expr.work]

/-- Every row pass has a fixed instruction stream, even when its row interval is empty. -/
theorem names_exact (w : ℕ) (S : Shape) (L : Layout) :
    names (program (w := w) S L) = 4589 := by
  norm_num only [program, names_seq, plane_names, dense_names, header_names, gather_names,
    route_names, leaf_names]

/-- The instructions for physically installing the immutable column are paid once. -/
theorem names_installed (w base n : ℕ) (fixed : ℕ → ℕ) (S : Shape) (L : Layout) :
    names ((DescentStaticWordColumn.program w base fixed n).seq (program (w := w) S L)) =
      15 * (n + 1) + 4589 := by
  rw [names_seq, DescentStaticWordColumn.names_mount, names_exact]


end Hierarchy.DescentTerminalEmitter

end OAI

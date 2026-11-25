import OAI.Optimization.LinearProgramming.PriceGame.ControlWireTrial
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingBounds

/-! The scratch arrays used in a trial frame. All bounds count the elements actually
serialized, including the expert-by-good allocation matrix and every earlier baseline. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)
open Trial

/-- Uniform numerical bounds for one run. `width` counts an encoded rational, `score`
an encoded natural score, and `logSize` the maximal number of probes in a cached result. -/
structure Envelope where
  depth : ℕ
  vertices : ℕ
  experts : ℕ
  width : ℕ
  score : ℕ
  logSize : ℕ

def RowFits (count width : ℕ) (row : List ℚ) : Prop :=
  row.length ≤ count ∧ ∀ q ∈ row, (ratCode q).length ≤ width

def MatrixFits (rows cols width : ℕ) (table : List (List ℚ)) : Prop :=
  table.length ≤ rows ∧ ∀ r ∈ table, RowFits cols width r

theorem row_le {n w : ℕ} {r : List ℚ} (h : RowFits n w r) :
    (listCode ratCode r).length ≤ rowBound n w := list_le _ _ h.1 h.2

theorem matrix_le {m n w : ℕ} {rows : List (List ℚ)} (h : MatrixFits m n w rows) :
    (listCode (listCode ratCode) rows).length ≤ listBound m (rowBound n w) :=
  list_le _ _ h.1 (fun r hr => row_le (h.2 r hr))

namespace Envelope

variable (e : Envelope)

def probeSize := probeBound e.depth e.vertices e.width
def resultSize := roundBound e.vertices e.experts e.score e.logSize e.probeSize e.width
def inputSize := pairBound e.depth (pairBound (historyBound e.depth e.vertices e.width) (rowBound e.experts e.width))
def preparedSize := pairBound 1 (pairBound (rowBound e.vertices e.width)
  (pairBound (listBound e.experts (rowBound e.vertices e.width)) (rowBound e.experts e.width)))
def completedSize := pairBound (rowBound e.vertices e.width) (pairBound (rowBound e.vertices e.width)
  (pairBound (rowBound e.experts e.width) e.resultSize))

structure InputFits (i : NodeInput) : Prop where
  level : i.level ≤ e.depth
  history : MatrixFits e.depth e.vertices e.width i.history
  weights : RowFits e.experts e.width i.weights

structure PreparedFits (p : Prepared) : Prop where
  baseline : RowFits e.vertices e.width p.baseline
  allocation : MatrixFits e.experts e.vertices e.width p.allocation
  deep : RowFits e.experts e.width p.deepWeights

structure ProbeFits (p : PackedProbe) : Prop where
  level : p.level ≤ e.depth
  prices : RowFits e.vertices e.width p.prices
  history : MatrixFits e.depth e.vertices e.width p.history

structure ResultFits (p : PackedRound) : Prop where
  prices : RowFits e.vertices e.width p.prices
  scores : p.scores.length ≤ e.experts
  score_width : ∀ s ∈ p.scores, s.bits.length ≤ e.score
  logs : p.log.length ≤ e.logSize
  log_rows : ∀ s ∈ p.log, e.ProbeFits s

structure CompletedFits (c : Completed) : Prop where
  baseline : RowFits e.vertices e.width c.baseline
  mapped : RowFits e.vertices e.width c.mapped
  gains : RowFits e.experts e.width c.gains
  child : e.ResultFits c.child

theorem input_length (i : NodeInput) (h : e.InputFits i) : (nodeInputCode i).length ≤ e.inputSize :=
  prod_le _ _ _ _ ((nat_le_self _).trans h.level) (prod_le _ _ _ _ (matrix_le h.history) (row_le h.weights))

theorem prepared_length (p : Prepared) (h : e.PreparedFits p) : (preparedCode p).length ≤ e.preparedSize :=
  prod_le _ _ _ _ le_rfl (prod_le _ _ _ _ (row_le h.baseline)
    (prod_le _ _ _ _ (matrix_le h.allocation) (row_le h.deep)))

theorem probe_length (p : PackedProbe) (h : e.ProbeFits p) : (packedProbeCode p).length ≤ e.probeSize :=
  prod_le _ _ _ _ ((nat_le_self _).trans h.level) (prod_le _ _ _ _ (row_le h.prices) (matrix_le h.history))

theorem result_length (p : PackedRound) (h : e.ResultFits p) : (packedRoundCode p).length ≤ e.resultSize :=
  prod_le _ _ _ _ (row_le h.prices) (prod_le _ _ _ _ (list_le _ _ h.scores h.score_width)
    (list_le _ _ h.logs (fun s hs => e.probe_length _ (h.log_rows s hs))))

theorem completed_length (c : Completed) (h : e.CompletedFits c) : (completedCode c).length ≤ e.completedSize :=
  prod_le _ _ _ _ (row_le h.baseline) (prod_le _ _ _ _ (row_le h.mapped)
    (prod_le _ _ _ _ (row_le h.gains) (e.result_length _ h.child)))

end Envelope
end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI

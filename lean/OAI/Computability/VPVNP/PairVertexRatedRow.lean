import OAI.Computability.VPVNP.PairVertexOrdinalReportCosts

/-! # A selected ordinal with the measurements of its physical root and role jobs -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM Compression DFS LocalHistory NetworkKernel NodeArguments TreeDecode
  TraversalRows
open CompressorRecords SourceTransport TerminalLink
open scoped Fin.CommRing

variable {k R : Type*} [Field k] [CommRing R] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → R) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (rowBase : ℕ)
    {geometry rootFields leaf shrink refresh : Segment} {p r w g : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r) (M : Machine w p r 11)
    (base grammar : ℕ) (order : Fin g ≃ B.Entry) (P : SiteParsers κ X.network)

local notation "exec₀" => B.execute κ hκ T hT X
local notation "data₀" => B.records κ hκ T hT X
local notation "chain₀" => StateExecution.termChain (exec₀) (data₀) z
local notation "readers₀" => selectedParsers B κ hκ T hT X z
local notation "trees₀" => selectedTrees B κ hκ T hT X z rowBase
local notation "Y" => StateExecution.finalState (exec₀) z
local notation "ord₀" => siteOrder (Y)
local notation "final₀" => finalParsers (chain₀) (readers₀) P
local notation "head₀" => TerminalLink.header (Machine.publicData M)
local notation "allow₀" => workerCell (head₀)

variable (half : ∀ u, ((B.execute κ hκ T hT X).finalState z).network.Half u)

local notation "selected₀" => siteOrdinals (final₀) (Order.entries (ord₀)) order half

variable (cap : ℕ) (m : Memory w) (i : Fin (siteOrder ((B.execute κ hκ T hT X).finalState
  z)).length)

local notation "rows₀" => OrdinalRows B κ hκ T hT X z rowBase A M base grammar order P half cap m i

open CursorNetwork


/-- Retains the measured prefix and the native local-role allowance on the
same memory and half-wire assignment as the classified returning paths. -/
structure RatedOrdinal (n power scan : ℕ) where
  /-- The selected ordinal's concrete vertex rows and parser inputs carried alongside their
  cost bounds. -/
  row : rows₀
  preProbes : countProbes row.pre ≤ 9 + 6 + 5 * S.baseDegree + incidentBits (Y) ((ord₀).entries i)
  preTicks : row.pre.length ≤ 44 + n ^ 3 + (15 + 21 * S.baseDegree + 5 * incidentBits (Y)
    ((ord₀).entries i))
  jobProbes : ∀ j, row.cost j → countProbes j.trace ≤ scan * (n.log2 + 1) ^ power
  jobTicks : row.maxTicks ≤ n ^ 43

variable {B κ hκ T hT X z rowBase A M base grammar order P half cap m i} {n power scan : ℕ}

/-- The bound for a specific successful source report, including the
margin for both physical controllers. -/
theorem RatedOrdinal.report_cost (q : RatedOrdinal B κ hκ T hT X z rowBase A M base grammar order P
      half cap m i n power scan) (link : Contains A M)
    (hn : 2048 ≤ n) (degree : S.baseDegree ≤ n) (labels : Fintype.card B.Entry ≤ n)
    (width : (Y).maxWireWidth ≤ n) (visits : (chain₀).occurrences (fun _ => 1) ((ord₀).entries i)
      ≤ n)
    (x : (selected₀).Choice i) (r : Report w) (run : execute M.program cap
      (M.program.start (i.val : Word w)) m ((selected₀).encode i x) = some r) :
    1 + r.probes ≤ siteAccesses (Y) (chain₀)
      (VertexReportBudget.coefficient S.baseDegree (Fintype.card B.Entry) 6 scan 0 0)
      power n ((ord₀).entries i) ∧ r.events.length + 107 ≤ n ^ 45 :=
  q.row.ordinalChecks B κ hκ T hT X z rowBase A M base grammar order P half link n power 6 scan
    hn degree labels width visits q.preProbes q.preTicks q.jobProbes q.jobTicks x r run

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI

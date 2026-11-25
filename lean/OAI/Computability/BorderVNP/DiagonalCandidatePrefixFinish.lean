import OAI.Computability.BorderVNP.DiagonalPrefixFinishRun
import OAI.Computability.BorderVNP.DiagonalGuardedReportTransport
import OAI.Computability.BorderVNP.DiagonalReceivedReportLayoutCast
import OAI.Computability.BorderVNP.CubePhysicalReceivedReportReaders

/-! # All subtotal proposals on the same routed positive assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize DiagonalTallyCellReports RoutingISA DiagonalResidueRAM
open TeamContraction.ProcessorSlots TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields
open RoutingISA.SignedTaskArena RoutingISA.Evaluator FiniteEvaluator NativeAssignments
open CompactMachine CellMacro.Generator

set_option autoImplicit false
set_option quotPrecheck false

variable {D B w n : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    (sa : SignedTaskArena.Layout) {gen : Fragment IO} {reserve groups cap width : ℕ}
    (X : UncheckedCandidate sa.id gen n w sa.cube.teams sa.dim width)
    (p : PositiveFields reserve sa.cube.n groups cap sa.cube.teams sa.dim width)
    {cell : N.Site → Fin sa.cube.cells}
    (slot : LiveBit N cell ↪ Slot sa.cube.n sa.cube.header.d sa.cube.header.blocks (sa.cube.h*sa.cube.b))
    (tags : N.Tables (Entry (Fin sa.p.parameters) (Fin sa.p.report.gadgets))) (x : Ports bits)
    (id : TableEntry sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s → Fin sa.p.report.gadgets)
    (words : PowerWords (Fin sa.cube.teams) (Fin sa.p.parameters) (Fin sa.p.report.gadgets) B N tags)
    (label : Fin sa.cube.cells → Label (sa.cube.n+1) sa.cube.header.d)
    (owner : Fin sa.cube.header.d → Fin sa.cube.teams)
    (a : Path N cell sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s)
    (control fieldWidth bodyCap : ℕ) (A : Fin sa.cube.teams → StartupArena)
local notation3 (prettyPrint := false) "guards" => ∀ t c,c∈X.assigned t → c.Passing w n
local notation3 (prettyPrint := false) "claim" => Fin (sa.cube.teams*sa.dim*width) → Bool
local notation3 (prettyPrint := false) "S(" ok "," raw "," t ")" => X.team (canonicalReports X.assigned ok) raw t
local notation3 (prettyPrint := false) "pr(" ok "," raw "," t ")" => (X.candidate (canonicalReports X.assigned ok) raw).1 t
local notation3 (prettyPrint := false) "layout(" ok "," raw "," t ")" =>
  reportLayout sa.before sa.after (Fin.val ((S(ok,raw,t)).pub 0)) control
    sa.p.parameters fieldWidth bodyCap sa.cube.stop
variable (rc : ∀ (ok : ∀ u c, c ∈ X.assigned u → c.Passing w n)
      (raw : Fin (sa.cube.teams * sa.dim * width) → Bool) (t : Fin sa.cube.teams),
    ReceivedRows (fun _ : Fin sa.cube.teams =>
      reportLayout sa.before sa.after ((X.team (canonicalReports X.assigned ok) raw t).pub 0).val
        control sa.p.parameters fieldWidth bodyCap sa.cube.stop) sa.cube.cells)
    (hosts : ∀ ok raw t (j : (u : Fin sa.cube.teams) × Fin ((rc ok raw t).cells u).length),
      pathCellOwner label owner a ((rc ok raw t).order j)=j.1)
    (tapes : ∀ ok raw t u, ReportTape ((rc ok raw t).cells u))
local notation3 (prettyPrint := false) "stream(" ok "," raw "," t ")" => fun (u : Fin sa.cube.teams) (j : ℕ) =>
  if h : j<(reportBits ((rc ok raw t).cells u)).length then tapes ok raw t u ⟨j,h⟩ else false
local notation3 (prettyPrint := false) "order(" ok "," raw "," t ")" =>
  (rc ok raw t).ledgerOrder tags words label owner a (hosts ok raw t) t

/-- On a fixed mathematical path, the canonical native report and every raw
subtotal proposal use the same row of exponents. Each run and each returned
reader refer to the genuine selected prefix and the same received directory. -/
theorem returnedFinish_of_prefixRuns
    (_runs : ∀ ok raw t, PrefixFinishRun sa (S(ok,raw,t)) (pr(ok,raw,t)) control fieldWidth bodyCap
      id owner a (rc ok raw t) t (tapes ok raw t) (A t) (p.withSubtotals raw))
    (_reads : ∀ ok raw t, ReportReaders slot tags x words label owner a t
      (Orders.withNativeVertices tags words label owner a t (order(ok,raw,t)))
      ((rc ok raw t).reportedWithTape (stream(ok,raw,t)) (fun _ => 0)))
    (counts : Fin sa.cube.teams → Fin sa.dim → ℕ)
    (_numbered : physicalRow slot tags x (fun (_ : Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks) => id)
      words label owner a=counts)
    (_bounded : ∀ t c,counts t c<2^w) : X.ReturnedFinish p counts (fun _ => sa) A := by
  intro ok raw t
  obtain ⟨i,post,_,_,kept,_,frame,place⟩ := PrefixFinishRun.targetReceipt sa
    (X.team (canonicalReports X.assigned ok) raw t) ((X.candidate (canonicalReports X.assigned ok) raw).1 t)
    control fieldWidth bodyCap slot tags x id words label owner a (rc ok raw t) (hosts ok raw t) t
    (tapes ok raw t) (A t) (p.withSubtotals raw) (_runs ok raw t) (_reads ok raw t) counts _numbered (_bounded t)
  exact ⟨i,post,kept,frame,place⟩

section Canonical
variable (fr : ℕ)
local notation3 (prettyPrint := false) "chart" f =>
  reportLayout sa.before sa.after f control sa.p.parameters fieldWidth bodyCap sa.cube.stop
variable (R : ReceivedRows (fun _ : Fin sa.cube.teams =>
      reportLayout sa.before sa.after fr control sa.p.parameters fieldWidth bodyCap sa.cube.stop) sa.cube.cells)
    (proposal : NativeReports X.assigned → ∀ u,ReportAssignments (R.cells u))
    (host : ∀ j : (u : Fin sa.cube.teams) × Fin (R.cells u).length, pathCellOwner label owner a (R.order j)=j.1)
    (frame : ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing w n) (raw : Fin (sa.cube.teams*sa.dim*width) → Bool)
      (t : Fin sa.cube.teams),fr=((X.team (canonicalReports X.assigned ok) raw t).pub 0).val)
local notation3 (prettyPrint := false) "E(" ok "," raw "," t ")" =>
  congrArg (fun f => chart f) (frame ok raw t)
local notation3 (prettyPrint := false) "actual(" ok "," raw "," t ")" => R.atLayout (E(ok,raw,t))
local notation3 (prettyPrint := false) "src(" ok ")" => proposal (canonicalReports X.assigned ok)
local notation3 (prettyPrint := false) "finiteTape(" ok "," u ")" =>
  (reportAssignmentEquiv (R.cells u)).symm (src(ok) u)
local notation3 (prettyPrint := false) "actualTape(" ok "," raw "," t ")" =>
  R.tapesAtLayout (E(ok,raw,t)) (fun u => finiteTape(ok,u))

/-- One canonical report reader per passing guard suffices for every subtotal
proposal, because the native prefix replays the same physical roster and its
finite report digits at its actual public frame. -/
theorem returnedFinish_of_canonicalReaders
    (runs : ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing w n) raw t, PrefixFinishRun sa (S(ok,raw,t)) (pr(ok,raw,t)) control fieldWidth bodyCap
      id owner a (actual(ok,raw,t)) t (actualTape(ok,raw,t)) (A t) (p.withSubtotals raw))
    (reads : ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing w n) t,
      R.pathReportReaders (N := N) (cell := cell) (B := B) slot tags x words label owner a host
        (R.sourceReportStream (src(ok))) (fun _ => 0) t)
    (counts : Fin sa.cube.teams → Fin sa.dim → ℕ)
    (numbered : physicalRow slot tags x (fun (_ : Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks) => id)
      words label owner a=counts)
    (bounded : ∀ t c,counts t c<2^w) : X.ReturnedFinish p counts (fun _ => sa) A :=
  returnedFinish_of_prefixRuns sa X p slot tags x id words label owner a control fieldWidth bodyCap A
    (fun ok raw t => actual(ok,raw,t)) (fun ok raw t => R.ownersAtLayout (E(ok,raw,t)) _ host)
    (fun ok raw t => actualTape(ok,raw,t)) runs
    (fun ok raw t => R.readersAtFrame sa control fieldWidth bodyCap (frame ok raw t) slot tags x words label owner a
      host t (src(ok)) (reads ok t)) counts numbered bounded

end Canonical
end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI

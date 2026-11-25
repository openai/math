import OAI.Computability.BorderVNP.DiagonalCandidatePrefixFinish

/-! # Native prefix runs on the original source, with its actual report tapes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger
open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyAllocation DiagonalTallyCellReports RoutingISA
open TeamContraction.ProcessorSlots TeamContraction.JointHeader RoutingISA.Evaluator RoutingISA.SignedTaskArena
open CompactMachine CellMacro.Generator NativeAssignments

set_option autoImplicit false
set_option quotPrecheck false

variable {D n w : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    (sa : SignedTaskArena.Layout) {gen : Fragment IO} {reserve groups cap width : ℕ}
    (p : PositiveFields reserve sa.cube.n groups cap sa.cube.teams sa.dim width)
    {cell : N.Site → Fin sa.cube.cells}
    (id : TableEntry sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s → Fin sa.p.report.gadgets)
    (owner : Fin sa.cube.header.d → Fin sa.cube.teams)
    (a : Path N cell sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s)
    (frame control fieldWidth bodyCap : ℕ) (A : Fin sa.cube.teams → StartupArena)
    (R : ReceivedRows (fun _ : Fin sa.cube.teams =>
      reportLayout sa.before sa.after frame control sa.p.parameters fieldWidth bodyCap sa.cube.stop) sa.cube.cells)
local notation3 (prettyPrint := false) "chart" f =>
  reportLayout sa.before sa.after f control sa.p.parameters fieldWidth bodyCap sa.cube.stop
local notation3 (prettyPrint := false) "native(" t "," u "," pr "," src "," cc "," h ")" =>
  PrefixFinishRun sa u pr control fieldWidth bodyCap id owner a (R.atLayout (congrArg (fun f => chart f) h)) t
    (R.tapesAtLayout (congrArg (fun f => chart f) h) (fun k => (reportAssignmentEquiv (R.cells k)).symm (src k)))
    (A t) (p.withSubtotals cc)

/-- A single real team and raw prefix admit the native finish setup on
their received tape at the true public frame. This is independent of which
proof identifies the allocated frame in the final candidate. -/
def OriginalPrefixRun (t : Fin sa.cube.teams) (u : PositiveTeam sa.id gen n w) (pr : u.Prefix)
    (src : ∀ k,ReportAssignments (R.cells k)) (cc : Fin (sa.cube.teams*sa.dim*width) → Bool) : Prop :=
  ∃ h : frame=(u.pub 0).val,Nonempty (native(t,u,pr,src,cc,h))

/-- Select the genuine run at the assigned frame equality. -/
theorem originalPrefixRun_at (t : Fin sa.cube.teams) (u : PositiveTeam sa.id gen n w) (pr : u.Prefix)
    (src : ∀ k,ReportAssignments (R.cells k)) (cc : Fin (sa.cube.teams*sa.dim*width) → Bool)
    (ok : OriginalPrefixRun sa p id owner a frame control fieldWidth bodyCap A R t u pr src cc)
    (h : frame=(u.pub 0).val) : Nonempty (native(t,u,pr,src,cc,h)) := by
  obtain ⟨_,run⟩ := ok
  exact run

/-- Every canonical subtotal candidate obtains its execution certificate from
the source run on that same returned report and the same prepared prefix. -/
noncomputable def prefixRunsOfOriginalReturns
    (X : UncheckedCandidate sa.id gen n w sa.cube.teams sa.dim width)
    (proposal : NativeReports X.assigned → ∀ k,ReportAssignments (R.cells k))
    (original : ∀ (r : NativeReports X.assigned) cc t,
      OriginalPrefixRun sa p id owner a frame control fieldWidth bodyCap A R t (X.team r cc t)
        ((X.candidate r cc).1 t) (proposal r) cc)
    (fr : ∀ (ok : ∀ u c,c∈X.assigned u → c.Passing w n) cc t,
      frame=((X.team (canonicalReports X.assigned ok) cc t).pub 0).val)
    (ok : ∀ u c,c∈X.assigned u → c.Passing w n) (cc : Fin (sa.cube.teams*sa.dim*width) → Bool)
    (t : Fin sa.cube.teams) :
    let r := canonicalReports X.assigned ok
    native(t,X.team r cc t,(X.candidate r cc).1 t,proposal r,cc,fr ok cc t) := by
  let r := canonicalReports X.assigned ok
  exact Classical.choice (originalPrefixRun_at sa p id owner a frame control fieldWidth bodyCap A R
    t (X.team r cc t) ((X.candidate r cc).1 t) (proposal r) cc (original r cc t) (fr ok cc t))

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI

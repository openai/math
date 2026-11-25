import OAI.Hierarchy.TraceReceiverPublishedWork
import OAI.Hierarchy.TraceFactorWork
import OAI.Hierarchy.TracePhysicalCharges
import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.ThreeFlat.Diagonal.PhysicalProgramLength
import OAI.ThreeFlat.Diagonal.PhysicalTreeResources

namespace OAI
/-! # Charging the native evaluator of an admitted physical terminal factor -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open scoped Classical

variable {F Pins : Type} [Field F] {d lanes : ℕ} {A : State d lanes}
variable (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (C : r.Charges)
variable (L : A.Words Pins) (N : Forest F L.ports.form) (start : A.Site → ℕ)

/-- The actual compiled tree's work, including all replay and copying, fits
in the terminal site's archived charge. -/
theorem work_charged (ordered : A.OrderedHalves L) (floor : r.LocalFloor C)
    (node : ∀ x,1+A.incidentWidth x ≤ start x) (width : ∀ x,L.ports.form.width x≤2*start x)
    (K : ℕ) (ge : 2≤K) (prices : r.FreshPath K h J C start)
    (seed : ∀ x,(N x).resources≤K*start x) (n : ℕ) (stages : r.StageLength n)
    (depth setup maps unitWork : ℕ)
    (tariff : (10025+1016*depth+setup+maps)*((2*n+1)*K)≤unitWork)
    (v : (r.plan.finish h).Site) :
    FactorWork.work r.plan h (r.wordAssembly J L) N depth setup maps v ≤ publishedWork r h C start unitWork v :=
  FactorWork.work_le_archive r.plan h (r.wordAssembly J L) N depth setup maps n K
    (r.chargeAt h C start v) unitWork v
    (r.assembled_resources h J C floor L ordered N start node width K ge prices seed n stages v) tariff

/-- Specialization to the physical block compiler. Each actual scheduled
move certifies its local charge floor and the program supplies the stage count. -/
theorem block_work_charged (B : Block F) (n rem : ℕ)
    (X : State (2^(B.exponent 0)) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem X).plan.History) (J : Run.WordSteps Pins ((B.repeat n).run rem X))
    (L : X.Words Pins) (N : Forest F L.ports.form) (start : X.Site → ℕ) (ord : X.OrderedHalves L)
    (node : ∀ x,1+X.incidentWidth x ≤ start x) (width : ∀ x,L.ports.form.width x≤2*start x)
    (K : ℕ) (ge : 2≤K) (prices : ((B.repeat n).run rem X).FreshPath K h J (B.charges n rem X) start)
    (seed : ∀ x,(N x).resources≤K*start x) (depth setup maps unitWork : ℕ)
    (tariff : (10025+1016*depth+setup+maps)*((2*(B.repeat n).length+1)*K)≤unitWork)
    (v : (((B.repeat n).run rem X).plan.finish h).Site) :
    let R := (B.repeat n).run rem X
    FactorWork.work R.plan h (R.wordAssembly J L) N depth setup maps v ≤
      publishedWork R h (B.charges n rem X) start unitWork v := by
  let R := (B.repeat n).run rem X
  exact work_charged R h J (B.charges n rem X) L N start ord
    ((B.repeat n).certified_floor _ (B.factor_bound n) rem X) node width K ge prices seed
    (B.repeat n).length ((B.repeat n).stageLength_run rem X) depth setup maps unitWork tariff v

variable [Fintype F]

/-- Running the contraction on its dense local record and pins returns the
actual selected cell on every branch within the charged terminal word. -/
theorem charged_factor {w : ℕ} (hw : 1≤w) (field : Fintype.card F*Fintype.card F≤2^w)
    (depth setup maps unitWork : ℕ) (v : (r.plan.finish h).Site)
    (cost : FactorWork.work r.plan h (r.wordAssembly J L) N depth setup maps v ≤ publishedWork r h C start unitWork v)
    (room : publishedWork r h C start unitWork v ≤ 2^w)
    (pins : (r.plan.assemble h (r.wordAssembly J L) N).1.width v ≤ 2^w)
    (input : Pins) (z : (r.plan.finish h).Half v) :
    let T := (r.plan.assemble h (r.wordAssembly J L) N).2 v
    let fit := FactorWork.factor_fits r.plan h (r.wordAssembly J L) N v depth setup maps hw field pins (cost.trans room)
    let code := RAM.Contraction.codec T.compile fit
    let machine := RAM.Contraction.machine (RAM.Contraction.parameters T.compile fit)
    let mem := RAM.BitLayout.memoryWithTail (fun _ => 0) T.compile code
      ((r.plan.assemble h (r.wordAssembly J L) N).1.read v input z) (fun _ => false)
    ∃ fuel ≤ publishedWork r h C start unitWork v,
      RAM.value code machine fuel 0 mem = r.plan.cells h (L.ports.form.values N input) v z ∧
      RAM.Subroutine.returnsBy machine.program (fun f _ _ out => f=0 ∧ out.isSome)
        fuel (machine.program.start 0) mem := by
  intro T fit code machine mem
  obtain ⟨fuel,bound,value,stop⟩ := FactorWork.native_factor r.plan h (r.wordAssembly J L) N
    v input z fit depth setup maps
  exact ⟨fuel,bound.trans cost,value,stop⟩

end Hierarchy.TraceDistribution.Physical

end
end OAI

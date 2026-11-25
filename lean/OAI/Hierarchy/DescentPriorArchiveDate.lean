import OAI.Hierarchy.DescentPublicDateMachine
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! Attach the actual native predecessor-register publisher to its public date. -/
namespace Hierarchy.DescentSixParty.Chronology.DateCode
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {w : ℕ}

/-- Insert a fixed, paid RAM pass immediately before the main instruction. -/
def withPriorArchive (p : NativePhase w) : DateCode w→DateCode w
  | .ordinary body t store u => .ordinary (p.program.seq body) (p.ticks+t) store u
  | .reset body t => .reset (p.program.seq body) (p.ticks+t)

theorem prior_archive_runs (p : NativePhase w) (d : DateCode w) (m out : Memory w)
    (one : p.Runs m) (rest : d.Runs (p.image m) out) (cost : d.cheap) :
    (withPriorArchive p d).Runs m out ∧ (withPriorArchive p d).cheap :=by
  cases d with
  | ordinary main t store u=>
    obtain ⟨mid,first,last⟩:=rest
    refine ⟨⟨mid,?_,last⟩,cheap_seq p.cheap cost.1,cost.2⟩
    intro P R K mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then one first mach pc reg pub exit rom advice cfg raw enter same
  | reset main t=>
    refine ⟨?_,cheap_seq p.cheap cost⟩
    intro P R K mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then one rest mach pc reg pub exit rom advice cfg raw enter same

theorem prior_archive_any (p : NativePhase w) (d : DateCode w) (base next limit : ℕ)
    (order : base≤next) (finish : next≤limit) (m : Memory w)
    (one : p.Runs m) (frame : ∀z,z<base ∨ next≤z→p.image m z=m z)
    (run : ∃out,d.Runs (p.image m) out ∧ d.cheap ∧
      ∀z,z<next ∨ limit≤z→ out z=p.image m z) :
    ∃out,(withPriorArchive p d).Runs m out ∧ (withPriorArchive p d).cheap ∧
      ∀z,z<base ∨ limit≤z→ out z=m z :=by
  obtain ⟨out,rest,cheap,held⟩:=run
  obtain ⟨time,cost⟩:=prior_archive_runs p d m out one rest cheap
  exact ⟨out,time,cost,fun z side=>(held z (side.imp_left (·.trans_le order))).trans
    (frame z (side.imp_right (finish.trans ·)))⟩

theorem prior_archive_price (p : NativePhase w) (d : DateCode w) :
    (withPriorArchive p d).tariff=(p.ticks+7*DescentStaticWordColumn.names p.program)*w+d.tariff :=by
  cases d <;> simp only [withPriorArchive,tariff,ticks,names,DescentStaticWordColumn.names_seq] <;> ring

end
end Hierarchy.DescentSixParty.Chronology.DateCode

end OAI

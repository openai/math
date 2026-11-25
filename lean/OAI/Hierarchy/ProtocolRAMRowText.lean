import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Exact native code size for a scan and a list of scanned columns -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
/-- Counts counters, temporary registers and public-word parameters. The bound
depends on the compiled row expression and is independent of the scanned extent. -/
def rowText (e : Expr) := 11+4*e.work

theorem text_scan (w first rows : ℕ) (e : Expr) : text (scan w first rows e)=rowText e := by
  obtain ⟨l,r,p⟩ := scan_size w first rows e
  unfold text rowText
  rw [l,r,p]
  omega

def listText (ps : List Pass) := 15+(ps.map (fun p=>rowText p.term)).sum

theorem text_passes (w : ℕ) (ps : List Pass) : text (program w ps)=listText ps := by
  induction ps with
  | nil => simp [program,listText,text_scan,rowText,Expr.work]
  | cons p ps ih =>
    simp only [program,text_seq,Pass.procedure,text_scan,ih,listText,List.map_cons,List.sum_cons]
    omega

end Hierarchy.ProtocolRAM.Calendar

end OAI

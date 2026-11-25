import OAI.Optimization.LinearProgramming.Compression.ServiceInspect
import OAI.Optimization.LinearProgramming.Compression.ServiceInspectBounds
import OAI.Optimization.LinearProgramming.Compression.ServiceSlotCompare

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM OracleSpec

/-- One fixed program prefix consumes an actual public minor request and finds its exact
generator coordinate. Its time bound is a dimension polynomial independent of history length. -/
theorem inspect_native {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (H : ℕ) (s : State ℚ) (u : MinorLog.Index D E)
    (hdim : d+e=n) (persist : Persistent D E J H s.memory) (hg : J.card≤(n+1)^6)
    (height : 50*(totalBits (MinorLog.entries D++MinorLog.entries E)+1)^6≤H) :
    ∃t l,l≤6000*(n+1)^13 ∧ Block.Eval (Memory.AllData (fun r => ratBits r≤H))
      (inspectRequest slotCompare) (MinorLog.resume s (MinorLog.words u.val)).memory l t ∧
      Inspected D E J (MinorLog.indexEquiv D E u) H t := by
  obtain ⟨hdet,hnat⟩ := inspectHeight_bound D E hdim hg
  obtain ⟨t,l,hl,ev,res⟩ := inspectRequest_spec slotCompare (fun m => 100*(m+1)) slotCompare_spec (fun _ => le_rfl)
    D E J H s u hdim persist (hdet.trans height) (hnat.trans height)
  exact ⟨t,l,hl.trans (inspectTime_bound n J.card hg),ev,res⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI

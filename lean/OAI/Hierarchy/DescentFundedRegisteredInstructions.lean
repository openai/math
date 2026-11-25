import OAI.Hierarchy.DescentRegisterTimelineCore
import OAI.Hierarchy.DescentCommonDateFamily

namespace OAI
/-! # The instruction array selected from a constant per-date program -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ} {Cut : ℕ→ Type*} (issue : ∀i,Cut i→ Position→ Move w→ Prop) (a : Position)

theorem fromCuts_date (i : ℕ) : DateCode.fromCuts Cut (fun j _=>date issue a j) i=date issue a i :=by
  classical
  by_cases present:Nonempty (Cut i)
  · simp [DateCode.fromCuts,present]
  · have missing : ¬∃m:Move w,(∃e:Cut i,issue i e (position issue a i) m) ∧
        (position issue a i).floor≤ m.next.floor :=by
      rintro ⟨m,⟨e,_⟩,_⟩
      exact present ⟨e⟩
    simp [DateCode.fromCuts,present,date,selected,missing]

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

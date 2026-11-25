import OAI.Hierarchy.DescentOrdinaryOriginalMarkBits
import OAI.Hierarchy.DescentOrdinaryMarkSignedInput
import OAI.Hierarchy.DescentIssuedSignedChart
import OAI.Hierarchy.DescentDatedMeter

namespace OAI
/-! The ordinary drawing and the signed program read the same marks on the issued shape. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentHostDegree DescentPacking.PackedMatch.Local.Stage
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem original_mark_identity (fit : Fintype.card v.prior.V≤v.area.H) (header payload M : ℕ)
    (roster : Fin v.area.H→Fin v.prior.placement.degree→Option (Fin v.area.H))
    (age : v.age<v.schedule.length) (radix : v.schedule.radix=2^v.k)
    (sizes : v.schedule.groupCount (v.age+1)*2^v.k=v.schedule.groupCount v.age) :
    v.withIssuedSigned.markBits v.issuedSignedChart fit sizes roster=
      (⟨v.area.H,fit,header,payload,M⟩ : MeterPort v.prior).originalMarks v.venue.hosts roster age radix :=by
  funext x j h g
  have read:=v.withIssuedSigned.markBits_original v.issuedSignedChart fit sizes roster age radix rfl x j h g
  have pitch : v.withIssuedSigned.materialPitch=(2^(v.k+1)-1)*(2^packExponent 20 v.prior.placement.degree+2) :=by
    change (2^(v.k+1)-1)*(2^packExponent 20 v.stage.Δ+2)=_
    rw [(Dated.Meter.ticket_shape v.ticket).2]
  rw [pitch] at read
  exact read

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

import OAI.Computability.NearSquareRoot.InterchangeTemplateData
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasPrimrec

/-! # One search over all finite interchange control tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template

open InterchangeROMRepair

namespace Data

variable {X : Type} [Primcodable X]

theorem primrec_valid {j t : X → ℕ} {x : X → Data} (hj : Primrec j) (ht : Primrec t) (hx : Primrec x) :
    PrimrecPred fun v => Valid (j v) (t v) (x v) := by
  let h (i) := (primrec_header i).comp hx
  have hp := primrec_modulusIndex.comp hx
  have hw := primrec_width.comp hx
  have hm := h 2
  have hlabel := TemplateMasks.primrec_matrix (primrec_mask.comp hx) (h 4) (h 5)
  have minor := NumericMinor.primrec_laws hp (h 4) (h 6) hlabel
    (Raw.primrec_read (h 6) (primrec_middle.comp hx)) (primrec_row.comp hx) (primrec_col.comp hx)
  have charts := FlatAtlas.primrec_valid (h 1) (h 3) hm (h 4) (h 5)
    (primrec_mask.comp hx) (primrec_chart.comp hx)
  have repair := Raw.primrec_valid hp (Raw.primrec_rowCount.comp hm) (Raw.primrec_checkCount.comp hm)
    hm (Sizes.primrec_pencilOrder.comp hm) (Raw.primrec_halfCode.comp hp) (primrec_repair.comp hx)
  have contract := TemplateCost.primrec_accept hj hm (h 3) (h 1) hw (primrec_calls.comp hx)
  exact (primrec_sizeChecks.comp ht hx).and ((primrec_degreeChecks.comp hx).and
    (minor.and ((Primrec.eq.comp charts (.const true)).and (repair.and (Primrec.eq.comp contract (.const true))))))

def enumerate (n : ℕ) : Data := (Encodable.decode n).getD default

@[simp] theorem enumerate_encode (x : Data) : enumerate (Encodable.encode x) = x := by
  simp [enumerate]

theorem primrec_enumerate : Primrec enumerate := Primrec.option_getD.comp Primrec.decode (.const _)

end Data
end Interchange.Template

end NearSquareRoot
end Computability
end OAI

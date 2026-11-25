import OAI.Computability.NearSquareRoot.InterchangeNumericMinor
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPRDecode

/-! # Packing the selected minor into three finite numerical tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.NumericMinor

open InterchangeROMRepair.Raw


theorem exists_encoding {p l h : ℕ} [Fact (p+1).Prime] (A : Mat) (c : MinorROM.Code (Fin l) (ZMod (p+1)) h)
    (hc : MinorROM.valid (interpret p l l A) c = true) :
    ∃ s t middle : List ℕ, s.length = h ∧ t.length = h ∧ laws p l h A (read h middle) s t := by
  obtain ⟨hi,hj,_,_⟩ := (MinorROM.valid_iff _ _).mp hc
  let s := encode c.row
  let t := encode c.col
  let hs := (picks_encode c.row).mpr hi
  let ht := (picks_encode c.col).mpr hj
  have eqs : selected s hs = c.row := funext fun i => Fin.ext (index_encode _ i)
  have eqt : selected t ht = c.col := funext fun i => Fin.ext (index_encode _ i)
  refine ⟨s,t,matrixTape c.middle,by simp [s,encode],by simp [t,encode],?_⟩
  apply (laws_iff _ _ s t hs ht).mpr
  simpa only [eqs,eqt,interpret_matrixTape] using hc

end Interchange.NumericMinor

end NearSquareRoot
end Computability
end OAI

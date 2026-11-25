import OAI.Computability.BorderVNP.DiagonalPositiveExteriorRoutes

/-! # Common header positions across different scheduled relay widths -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Diagonal.Layout Routing JointHeader

variable {R r link : ℕ} (L M : WireLayout (R+1) r link) (size : M.header=L.header)

include size

/-- The header is the literal prefix of each exterior block. Two schedules
may assign different lengths to both relay legs and still read the same
header from every physical exterior. -/
theorem observed_eq_of_header_length (ext : Exterior R r link → Bool) (b : Block (R+1)) :
    observed M ext b = observed L ext b := by
  apply List.ext_getElem (by simpa only [observed_length] using size)
  intro i hi hj
  let x : Fin M.header := ⟨i,hi.trans_eq (observed_length ..)⟩
  let y : Fin L.header := ⟨i,hj.trans_eq (observed_length ..)⟩
  have hp : M.position b (.inl x) = L.position b (.inl y) := Fin.ext rfl
  have same := congrArg (fun a : Fin (r*link) => ext (b,finProdFinEquiv.symm a)) hp
  exact (congrFun (observed_bits M ext b) x).trans (same.trans (congrFun (observed_bits L ext b) y).symm)

/-- Change the scheduled widths at a fixed physical header without touching
any of the raw wires, including wire bits outside the header. -/
def HeaderExterior.changeLayout (header : List Bool) : HeaderExterior L header ≃ HeaderExterior M header where
  toFun x := ⟨x.val,fun b => (observed_eq_of_header_length L M size x.val b).trans (x.property b)⟩
  invFun x := ⟨x.val,fun b => (observed_eq_of_header_length L M size x.val b).symm.trans (x.property b)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TeamContraction

end BorderVNP
end Computability
end OAI

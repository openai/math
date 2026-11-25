import OAI.Hierarchy.DescentResetStencilPitch

namespace OAI
/-! # Native stencil bounds at a smaller lane pitch of the same date -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentPlainTerminal.Suffix DescentSIMDLookup DescentPackedColony

theorem widths_of_packed (S : StencilBook) (h : ℕ) (positive : 1≤S.M)
    (fit : sharedWidth S*S.M≤h/2) (cutoff : S.levels+S.total≤h/2) : StencilBook.Widths S h :=by
  let w:=sharedWidth S
  have paid (a : ℕ) (small : a≤w) : a*S.M≤h/2 :=(Nat.mul_le_mul_right _ small).trans fit
  have reserved : widthUnit S≤w:=Nat.le_max_left ..
  have bounds:=max_le_iff.mp reserved
  have pp:=max_le_iff.mp bounds.1
  have stencilBounds:=max_le_iff.mp bounds.2
  have shape:=max_le_iff.mp stencilBounds.2
  have tail:=max_le_iff.mp shape.2
  have n:S.n≤w:=(Nat.le_add_left ..).trans stencilBounds.1
  have c:S.n≤h/2:=(Nat.le_mul_of_pos_right _ positive).trans (paid _ n)
  have bits:2^S.r*S.m≤w:=by nlinarith only [shape.1,Nat.zero_le (2^S.r)]
  refine ⟨paid _ pp.1,cutoff,?_,?_,paid _ stencilBounds.1⟩
  · dsimp [Stencil.ReaderTables.largest]
    exact max_le c (max_le (paid _ pp.2) (max_le (paid _ tail.2) (paid _ bits)))
  · apply paid
    nlinarith only [shape.1]

end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI

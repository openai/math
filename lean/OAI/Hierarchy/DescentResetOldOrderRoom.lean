import OAI.Hierarchy.DescentResetDateStencil

namespace OAI
/-! The comparison expression of the issued stencil fits its dated address
range before a basis or an execution has been selected. -/
namespace Hierarchy.DescentPlainTerminal.Suffix.StencilBook
open DescentSIMDLookup DescentGL DescentColonies ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

theorem order_fit_of_geometry (S : StencilBook) (X : Sources) (base out g : ℕ) {w : ℕ}
    (geometry : Geometry S X base out w) (capacity : S.endAddress base<2^w) (word : S.n*S.M≤w)
    (i x : ℕ) : (S.orderExpr X base out g i x).Fits w (S.endAddress base) := by
  let C:=S.readers base
  let P:=S.inputs X base out g
  have last : C.stop≤S.endAddress base:=by
    let L := S.last base
    have table : C.stop ≤ L.table := Nat.le_add_right ..
    have mask : L.table ≤ L.mask := Nat.le_add_right ..
    have scratch : L.mask ≤ L.scratch := Nat.le_add_right ..
    have out : L.scratch ≤ L.out := Nat.le_add_right ..
    exact (((table.trans mask).trans scratch).trans out).trans (Nat.le_add_right ..)
  have early : C.origin≤S.endAddress base:=C.before_planes.trans (C.plane_le.trans last)
  have operands:=S.fit X base out g geometry
  have planes (j : Fin C.m) : (P.planes j).Fits w (S.endAddress base):=
    ProtocolRAMGeneratedWrite.fits_mono _ early (operands.planes j)
  obtain ⟨_,installed,_,_⟩:=C.issue_readers P (S.endAddress base) (fun _=>0 : Memory w)
    last capacity word planes
  let atBlock (z : ℕ) : Block C.r:=⟨z%2^C.r,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  exact Stencil.fields_fit C P operands early _ installed (.inr (.inr (.inl (atBlock i,atBlock x))))

end
end Hierarchy.DescentPlainTerminal.Suffix.StencilBook

namespace Hierarchy.DescentSixParty.PackedFlow.ResetMiddle
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM

theorem order_fit (P : ResetMiddle) {w : ℕ} (room : P.Room w) (i x : ℕ) :
    (P.S.orderExpr P.X P.base P.bank P.g i x).Fits w P.endAddress :=
  P.S.order_fit_of_geometry P.X P.base P.bank P.g room.operands room.total room.word i x

end Hierarchy.DescentSixParty.PackedFlow.ResetMiddle

end OAI

import OAI.Hierarchy.DescentResetSignedHaloTariff

namespace OAI
/-! # Contiguous allocation of the signed halo date from a single public offset -/
namespace Hierarchy.DescentResetSignedHaloMatrix
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section

def arrange (root H S D cap G M t a b : ℕ) (count owner old : Bank) : Shelf:=
  let n:=H*(D+1)
  let matrix:=root+cells H D
  let decodeAt:=matrix+DescentResetOriginalSlots.stride n
  ⟨count,old,owner,⟨matrix,Nat.clog 2 n⟩,root,decodeAt,decodeAt+2*2^(t*M),H,S,D,cap,G,M,t,a,b⟩

theorem arrange_fits {root H S D cap G M t a b w : ℕ} {count owner old : Bank}
    (cf : count.Fits w root) (of_ : owner.Fits w root) (rf : old.Fits w root)
    (hs : H<2^w) (os : S<2^w) (ds : D+1<2^w) (len : S*D≤old.size)
    (space : (arrange root H S D cap G M t a b count owner old).high+H*chunks G M<2^w) :
    (arrange root H S D cap G M t a b count owner old).Fits w:=by
  let C:=arrange root H S D cap G M t a b count owner old
  have high : C.high<2^w:=(Nat.le_add_right ..).trans_lt space
  have top : C.lookupAt≤C.high:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have mid : C.decodeAt≤C.lookupAt:=Nat.le_add_right ..
  have inside : C.ranks.base+C.ranks.size=C.decodeAt:=rfl
  have end_ : C.decodeAt<2^w:=mid.trans_lt (top.trans_lt high)
  have rows : H*(D+1)≤C.ranks.size:=DescentResetOriginalSlots.rows_le _
  refine ⟨⟨cf,of_,rf,le_rfl,?_,hs,os,ds,len⟩,?_,rows,le_rfl,space⟩
  · exact (Nat.add_le_add_left rows _).trans_lt (inside.le.trans_lt end_)
  · exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (inside.le.trans_lt end_),inside.le⟩

theorem arrange_extent (root H S D cap G M t a b : ℕ) (count owner old : Bank) :
    (arrange root H S D cap G M t a b count owner old).high=
      root+3*DescentResetOriginalSlots.stride (H*(D+1))+2*2^(t*M)+
      DescentPackedChildNeighbor.SIMD.ROM.cells (D+1) a b M H G+2^DescentPackedChildNeighbor.SIMD.ROM.rowBits H G M:=by
  simp only [arrange,Shelf.high,cells,DescentPackedChildNeighbor.SIMD.ROM.output]
  omega

end
end Hierarchy.DescentResetSignedHaloMatrix

end OAI

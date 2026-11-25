import OAI.Hierarchy.DescentOrdinaryReferenceInputs
import OAI.Hierarchy.DescentOrdinaryOriginMask

namespace OAI
/-! Ordinary operand pages use a single actor census at each returned low ordinal. -/
namespace Hierarchy.DescentPackedZip
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
theorem source_unique {w H G M a : ℕ} {m : Memory w} {e : Expr}
    {x y : Fin H→Fin G→Cell a} (hm : 0<M) (fit : 2^(a*M)≤2^w)
    (lhs : Source e x M m) (rhs : Source e y M m) : x=y :=by
  funext h g
  let p:=position h g hm
  let j:=lane g hm
  have address : p.2.val*M+j.val=g.val:=Nat.div_add_mod' ..
  have same:= (lhs p).symm.trans (rhs p)
  have numbers := congrArg Fin.val same
  rw [Fin.val_cast_of_lt ((data x p).isLt.trans_le fit),Fin.val_cast_of_lt ((data y p).isLt.trans_le fit)] at numbers
  have packed : data x p=data y p:=Fin.ext numbers
  have lanes:=congrFun ((encode a M).injective packed) j
  have host : p.1 = h := rfl
  simpa only [address,dite_eq_left g.isLt,host] using lanes
end Hierarchy.DescentPackedZip

namespace Hierarchy.DescentOrdinaryReferenceInputs.Directory
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryOriginMask DescentOperandVectorArena
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

theorem marked_pages {C : DescentOrdinaryRefsROM.Chart} {L : Layout} (dir : Directory C L)
    {H G K' a nb mb M base w : ℕ} {m : Memory w} (hm : 0<M)
    (pg other : Fin L.pageCount) (q : Fin L.lows)
    (x y : Values C.degree C.k C.oldNodes C.capacity H G a nb mb)
    (first : Measured (dir.refs pg q) x K' M base m)
    (second : Measured (dir.refs other q) y K' M base m) :
    marked x=marked y :=by
  have room:=first.emitFits.shift.2.1
  rw [Bank.size,first.emitFits.shiftBits] at room
  exact DescentPackedZip.source_unique hm room.le (read_mask _ _ first).2 (read_mask _ _ second).2

end Hierarchy.DescentOrdinaryReferenceInputs.Directory

end OAI

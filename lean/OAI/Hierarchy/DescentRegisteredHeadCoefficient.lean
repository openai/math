import OAI.Hierarchy.DescentDatedOperandHeadRows
import OAI.Hierarchy.DescentDatedOrdinaryRasterExtent
import OAI.Hierarchy.DescentSelectorWordScale
import OAI.Hierarchy.DescentMouthNumericBounds

namespace OAI
/-! One height-independent exponent for both authentic pre-selector head transfers. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentArgumentWidthArithmetic DescentCompiler.TerminalScale DescentDatedAddressBook DescentDatedOperandReadPipeline
open DescentHaloWalkRAM
noncomputable section

private theorem head_bound {U n f : ℕ} (large : 8192≤U) («fields» : n≤U^8) (work : f≤U^6) :
    headCoefficient n f≤U^19 :=by
  have base : 2≤U:=by omega
  have s {m : ℕ} (hm : m≤8192) : m≤U^1:=one (hm.trans large)
  have first:=mul (mul (s (by decide : 4≤8192)) (s (by decide : 4096≤8192)))
    (add base «fields» (s (by decide : 1≤8192)))
  have workA:=add base (s (by decide : 4≤8192))
    (add base (mul (s (by decide : 2≤8192)) work) (s (by decide : 4≤8192)))
  have workB:=mul (s (by decide : 7≤8192))
    (add base (s (by decide : 11≤8192)) (mul (s (by decide : 4≤8192)) work))
  exact add base (add base first (s (by decide : 109≤8192))) (mul «fields» (add base workA workB))

variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
theorem head_unit_at_scale (J a short : ℕ) (selected : v.signed=v.signedLayout.format v.payload)
    (lows : v.vector.lows=StageVenueTail.OrdinaryRaster.shapes v.area)
    (bought : ∀i,v.ticketReadGeometry.coefficientInputs 32 short i≤ scale J a)
    (localQ : v.vector.lows≤ scale J a) :
    v.headUnit≤ scale J (20*a) :=by
  let U:=scale J a
  let fmt:=v.ticket.depotShape v.short
  let P:=breadth fmt.degree
  have large : 8192≤U:=bought 0
  have base : 2≤U:=by omega
  have s {m : ℕ} (hm : m≤8192) : m≤U^1:=one (hm.trans large)
  have paths : P≤U^1:=one (bought 1)
  have blocks : fmt.blocks≤U^1:=one (bought 2)
  have degree : fmt.degree+1≤U^1:=one (bought 3)
  have wires : fmt.cap≤U^1:=one (bought 4)
  have lower : v.signed.lowSites≤2*v.vector.lows:=by
    rw [selected,lows]
    change 2^(v.k+1)*_≤2*((2^(v.k+1)-1)*_)
    rw [←Nat.mul_assoc]
    apply Nat.mul_le_mul_right
    have pos:=Nat.two_pow_pos (v.k+1)
    omega
  have peers : v.signed.peerKinds≤U^4 :=by
    have ds : v.signed.reach=P:=by rw [selected];rfl
    change (v.signed.reach*v.signed.reach)*v.signed.lowSites≤_
    rw [ds]
    exact mul (mul paths paths) (lower.trans (mul (s (by decide : 2≤8192)) (one localQ)))
  have old:=mul paths (mul blocks (mul ((Nat.le_succ _).trans degree) wires))
  have anchor:=mul paths (mul blocks (mul wires (s (by decide : 3≤8192))))
  have raw:=mul paths (mul blocks (mul wires (s (by decide : 11≤8192))))
  have wide : v.wideHeads.n≤U^8:=add base (mul blocks (mul (s (by decide : 4≤8192)) old))
    (add base (mul blocks (mul (s (by decide : 5≤8192)) anchor)) (mul blocks (mul (s (by decide : 8≤8192)) raw)))
  have narrow:=add base (mul paths degree) paths
  have bigger : 0<U:=by omega
  have upper:=add base (head_bound large wide (mul (s (by decide : 512≤8192)) (add base peers (s (by decide : 1≤8192)))))
    (head_bound large (raise bigger narrow (by decide : 3≤8)) (raise bigger (s (by decide : 512≤8192)) (by decide : 1≤6)))
  exact upper.trans_eq (DescentMouthNumericBounds.power_scale J a 20)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

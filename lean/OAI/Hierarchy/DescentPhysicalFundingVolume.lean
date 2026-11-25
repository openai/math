import OAI.Hierarchy.DescentPhysicalResetTailTariff
import OAI.Hierarchy.DescentResetSignedPagePrice
import OAI.Hierarchy.DescentOrdinaryOverlapReserve

namespace OAI
/-! Physical words touched by old-cost retile, the selected GL, and the new funded census. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentFundedCensus DescentSIMDLookup DescentSIMDLookup.Overlap DescentGLPacked DescentGLPacked.BankImage
open DescentGLPacked.BankImage.SignedFields DescentGLNielsen
noncomputable section

def fundingArea (s : DescentFundedCensus.Setup) (t : DescentFundedCensus.Shape) (h : ℕ):=
  1+Overlap.rows s.hosts s.oldGroups s.oldLanes+Overlap.rows s.hosts s.oldGroups s.gatherLanes+
    s.hosts*2^s.high+t.rows+2*(h+1)^2*2^(h/2)

def fundingFactor (s : DescentFundedCensus.Setup) (t : DescentFundedCensus.Shape) :=
  100000*(1+s.blocks+(schedule (s.high+s.low)).length)+
    1000*(1+t.jobs)*(100+roleWork s.capacity)

theorem funding_printed (s : DescentFundedCensus.Setup) (base w h : ℕ)
    (matrix : (s.high+s.low)*(s.high+s.low)≤h/2)
    (packed : (s.precision+s.precision)*2^s.low≤h/2) :
    let depth:=(schedule (s.high+s.low)).length
    s.printed base w≤depth+depth*2^(h/2)+(6*depth)*(2*(s.hosts*2^s.high+1)+2^(h/2)) :=by
  intro depth
  let C:=s.plan base
  have page:=Dated.pages (1*s.hosts) s.high s.low s.precision h packed
  have top:=Nat.mul_le_mul_left (6*depth) page
  have menus:=Nat.mul_le_mul_left depth (Nat.pow_le_pow_right (by decide : 0<2) matrix)
  change ((s.matrix base+depth+depth*2^((s.high+s.low)*(s.high+s.low)))-s.matrix base)+
    ((C.start+(6*depth)*2^(chartBits (1*s.hosts) s.high s.low s.precision))-C.start)≤_
  simp only [one_mul] at top ⊢
  omega

theorem funding_volume (s : DescentFundedCensus.Setup) (t : DescentFundedCensus.Shape) (base w h : ℕ)
    (prior : s.oldLanes≤h) (gather : s.gatherLanes≤h) (before : s.precision*s.oldLanes≤h/2)
    (matrix : (s.high+s.low)*(s.high+s.low)≤h/2)
    (packed : (s.precision+s.precision)*2^s.low≤h/2)
    (join : joinWidth s.precision s.blocks*s.gatherLanes≤h/2) (flag : s.flagWidth≤h/2)
    (short : t.width≤h/2) :
    setupCharge s base w+fundedCharge t s.capacity≤fundingFactor s t*fundingArea s t h :=by
  let A:=fundingArea s t h
  let n:=(schedule (s.high+s.low)).length
  have half: 2^(h/2)≤2*(h+1)^2*2^(h/2):=Nat.le_mul_of_pos_left _ (by positivity)
  have Apos:1≤A:=by dsimp [A,fundingArea];omega
  have table:2^(h/2)≤A:=by dsimp [A,fundingArea];omega
  have H:s.hosts*2^s.high+1≤A:=by dsimp [A,fundingArea];omega
  have rows:t.rows≤A:=by dsimp [A,fundingArea];omega
  have strips:s.stripCharge≤2048*A:=by
    apply Nat.mul_le_mul_left
    have q:=half_pages h s.oldGroups s.oldLanes s.gatherLanes s.precision prior gather before
    dsimp [A,fundingArea];omega
  have d:=funding_printed s base w h matrix packed
  have depth:n≤n*A:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n Apos
  have bound:s.printed base w≤20*n*A:=by
    change s.printed base w≤n+n*2^(h/2)+6*n*(2*(s.hosts*2^s.high+1)+2^(h/2)) at d
    have k:=Nat.mul_le_mul_left n table
    have q:=Nat.mul_le_mul_left (6*n) (Nat.add_le_add (Nat.mul_le_mul_left 2 H) table)
    nlinarith only [d,depth,k,q]
  have joined:2^(joinWidth s.precision s.blocks*s.gatherLanes)≤A:=
    (Nat.pow_le_pow_right (by decide) join).trans table
  have flags:2^s.flagWidth≤A:=(Nat.pow_le_pow_right (by decide) flag).trans table
  have census:2^t.width≤A:=(Nat.pow_le_pow_right (by decide) short).trans table
  have W:s.hosts*2^s.high≤A:=by omega
  have block : s.blocks≤ s.blocks*A:=by simpa using Nat.mul_le_mul_left s.blocks Apos
  have jobs : t.jobs≤t.jobs*A:=by simpa using Nat.mul_le_mul_left t.jobs Apos
  have str:=Nat.mul_le_mul_left s.blocks strips
  have jn:=Nat.mul_le_mul_left (2*s.blocks) joined
  have scan:=Nat.mul_le_mul_left (2*(1+s.blocks*18)+4) W
  have sw:=Nat.mul_le_mul_left (n*224) W
  have tbl:=Nat.mul_le_mul_left (2*(t.jobs+1)) census
  have roles:=Nat.mul_le_mul_left (t.jobs*(2*(3*(roleWork s.capacity+2)+22)+4)) rows
  have roleTerm:=Nat.mul_le_mul_left (t.jobs*(11+4*(3*(roleWork s.capacity+2)+22))) Apos
  have nameTerm:=Nat.mul_le_mul_left (11+4*(1+s.blocks*18)) Apos
  change _≤fundingFactor s t*A
  simp only [setupCharge,fundedCharge,DescentFundedCensus.Shape.pageCount,
    DescentFundedCensus.Setup.passesTime,DescentFundedCensus.Setup.passesNames,
    DescentFundedCensus.Setup.fieldWork,fundingFactor]
  change _≤(100000*(1+s.blocks+n)+1000*(1+t.jobs)*(100+roleWork s.capacity))*A
  dsimp only [n] at *
  nlinarith only [Apos,table,flags,depth,block,jobs,str,jn,scan,sw,tbl,roles,roleTerm,nameTerm,bound]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI

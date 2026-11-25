import OAI.Hierarchy.DescentOrdinaryPaletteTariff
import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentOrdinaryOverlapReserve

namespace OAI
/-! The primitive ROM and row invoice after charging each genuine packed date at its actual occupancy. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open DescentSIMDLookup DescentDatedSeedStartup DescentOrdinaryRoleRetile
set_option quotPrecheck false
noncomputable section
variable (L : DescentOrdinaryPrimitiveCheckpoint.Layout)
def control (h : ℕ) :=(h+1)^2*2^(h/2)*h
def liveVolume (h unit : ℕ) :=h+L.hosts*h+L.hosts*L.oldGroups*unit
def volume (h unit : ℕ) :=L.liveVolume h unit+control h

/-- A word width is charged to genuine rows once per port or local block, across all group copies. -/
structure Filled (h unit M : ℕ) : Prop where
  positive : 0<M
  ceiling : M≤h
  occupied : h≤M*unit

structure Funding (h unit : ℕ) : Prop where
  old : Filled h unit L.priorLanes
  newborn : Filled h unit L.birthLanes
  ranks : Filled h unit L.originLanes
  working : Filled h unit L.workLanes
  large : Filled h unit L.oldWork
  held : Filled h unit L.nextLanes
  oldKey : L.prior.bits*L.prior.beforeLanes≤h/2
  newbornKey : L.births.bits*L.births.beforeLanes≤h/2
  originKey : L.origins.bits*L.origins.beforeLanes≤h/2
  durableKey : L.durable.bits*L.durable.beforeLanes≤h/2
  projection : (L.references 0).digitBits≤h/2
  gates : (L.references 0).width≤h/2
  spread : L.spread.bits*L.blocks*L.workLanes≤h/2
  selection : L.join.width≤h/2

private def Paid (h V a c : ℕ) :=a*h≤c*V
private theorem addPaid {h V a b c d : ℕ} (x : Paid h V a c) (y : Paid h V b d) : Paid h V (a+b) (c+d):=by
  simpa only [Paid,Nat.add_mul] using Nat.add_le_add x y
private theorem mulPaid (n : ℕ) {h V a c : ℕ} (x : Paid h V a c) : Paid h V (n*a) (n*c):=by
  simpa only [Paid,Nat.mul_assoc] using Nat.mul_le_mul_left n x

variable (h unit : ℕ)
local notation "V" => L.volume h unit
local notation "t" => L.lows+1
private theorem onePaid (n : ℕ) : Paid h V n n:=Nat.mul_le_mul_left n (by unfold volume liveVolume;omega)

private theorem halfPaid {a : ℕ} (exponent : a≤h/2) : Paid h V (2^a) 1:=by
  have up:=Nat.mul_le_mul_right h (Nat.pow_le_pow_right (by decide : 0<2) exponent)
  have raw : 2^(h/2)*h≤control h:=by
    unfold control
    have m:1≤(h+1)^2:=Nat.one_le_pow _ _ (by omega)
    nlinarith only [Nat.mul_le_mul_right (2^(h/2)*h) m]
  exact up.trans (by change _≤1*(_+control h);omega)

private theorem rowPaid {hosts groups M : ℕ} (h₀ : hosts≤(t)*L.hosts) (g₀ : groups≤L.oldGroups)
    (fill : Filled h unit M) : Paid h V (hosts*chunks groups M) (t):=by
  have measured:=chunk_work hosts groups M h unit fill.occupied
  have scaled:=Nat.mul_le_mul_right h h₀
  have cost:=Nat.mul_le_mul_right unit (Nat.mul_le_mul h₀ g₀)
  unfold Paid volume liveVolume
  nlinarith only [measured,scaled,cost,Nat.zero_le (control h)]

private theorem lookupPaid (R : DescentOrdinaryRoleRetile.Layout) (lo : Filled h unit R.beforeLanes)
    (hi : Filled h unit R.afterLanes) (key : R.bits*R.beforeLanes≤h/2) :
    Paid h V R.lookupBill 2:=by
  have bound:=Nat.mul_le_mul_right h (Overlap.half_pages h R.groups R.beforeLanes R.afterLanes R.bits lo.ceiling hi.ceiling key)
  unfold Paid volume control
  change _≤_
  unfold DescentOrdinaryRoleRetile.Layout.lookupBill
  nlinarith only [bound,Nat.zero_le (L.liveVolume h unit)]

def retileFactor (blocks lows : ℕ) :=4096*(2+(blocks+1)*(3*(lows+1)+1))
private theorem retilePaid (R : DescentOrdinaryRoleRetile.Layout) (H : R.hosts≤(t)*L.hosts)
    (G : R.groups≤L.oldGroups) (lo : Filled h unit R.beforeLanes) (hi : Filled h unit R.afterLanes)
    (key : R.bits*R.beforeLanes≤h/2) (real : 0<R.hosts) :
    Paid h V (lookupFee R) (retileFactor R.blocks L.lows):=by
  have a:=L.rowPaid h unit H G lo
  have b:=L.rowPaid h unit H G hi
  have cells : Overlap.pieces R.groups R.beforeLanes R.afterLanes≤R.hosts*chunks R.groups R.beforeLanes:=
    (Nat.min_le_left ..).trans (Nat.le_mul_of_pos_left _ real)
  have third : Paid h V (Overlap.pieces R.groups R.beforeLanes R.afterLanes) (t):=
    (Nat.mul_le_mul_right h cells).trans a
  have row:=addPaid (addPaid (addPaid a b) third) (L.onePaid h unit 1)
  have all:=mulPaid 4096 (addPaid (L.lookupPaid h unit R lo hi key) (mulPaid (R.blocks+1) row))
  simpa only [lookupFee,retileFactor,DescentOrdinaryRoleRetile.Layout.rowBill,DescentOrdinaryRoleRetile.Layout.rows,
    show t+t+t+1=3*(t)+1 by omega] using all

/-- This coefficient uses only the previous and next local public degrees, block count, node capacity and donor slots. -/
def wordFactor :=
  let T:=L.lows+1
  let oldLength:=L.ports*T+(1+(T+L.ports))
  let refs:=L.references 0
  let count:=L.blocks*(T:ℕ)
  let cells:=L.blocks+2*count
  let K:=1+L.candidates*61
  let spread:=(4+L.lows*(4+T*(2*K+4)))+((4+10*cells)+(4+count*54))+
    7*((15+L.lows*(11+4*K))+(15*(cells+1)+111))
  let join:=(4+10*(2*1))+(4+L.blocks*(4+T*(2*25+4)))+7*((15*(2*1+1))+(15+L.blocks*(11+4*25)))
  retileFactor L.blocks L.lows+retileFactor L.fields L.lows+retileFactor L.blocks L.lows+
    literalFee oldLength+(literalFee refs.oldNodes+literalFee refs.count)+spread+join+retileFactor L.blocks L.lows

private theorem literalPaid {a f : ℕ} (x : Paid h V a f) : Paid h V (literalFee a) (literalFee f):=
  addPaid (addPaid (L.onePaid h unit 4) (mulPaid 10 x))
    (mulPaid 7 (mulPaid 15 (addPaid x (L.onePaid h unit 1))))

theorem word_fee (room : L.Funding h unit) (hosts : 0<L.hosts) (lows : 0<L.lows) :
    L.paid*h≤L.wordFactor*L.volume h unit:=by
  have H : L.hosts≤(t)*L.hosts:=Nat.le_mul_of_pos_left _ (by omega)
  have H' : L.successors≤(t)*L.hosts:=by unfold successors;rw [Nat.mul_comm];exact Nat.mul_le_mul_right _ (by omega)
  have positive : 0<L.successors:=Nat.mul_pos hosts lows
  have J : L.groups≤L.oldGroups:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have first:=L.retilePaid h unit L.prior H le_rfl room.old room.large room.oldKey hosts
  have second:=L.retilePaid h unit L.births H le_rfl room.newborn room.large room.newbornKey hosts
  have third:=L.retilePaid h unit L.origins H' J room.ranks room.working room.originKey positive
  have last:=L.retilePaid h unit L.durable H' J room.working room.held room.durableKey positive
  have oldRows:=L.rowPaid h unit H (le_refl L.oldGroups) room.large
  have source:=L.rowPaid h unit H J room.working
  have target:=L.rowPaid h unit H' J room.working
  have host : Paid h V L.hosts 1:=by unfold Paid volume liveVolume;omega
  have steps:=addPaid (mulPaid L.ports oldRows) (addPaid host (addPaid oldRows (by
    simpa only [Nat.mul_comm L.ports L.hosts,Nat.mul_one] using mulPaid L.ports host)))
  have port:=L.literalPaid h unit steps
  have rowNum:=mulPaid L.blocks target
  have folded:=addPaid (mulPaid L.blocks (L.halfPaid h unit room.spread)) (mulPaid 2 rowNum)
  have nodes:=mulPaid (L.references 0).oldNodes (L.halfPaid h unit room.projection)
  have gates:=mulPaid (L.references 0).count (L.halfPaid h unit room.gates)
  have refs:=addPaid (L.literalPaid h unit nodes) (L.literalPaid h unit gates)
  let K:=1+L.candidates*61
  have scan:=addPaid (L.onePaid h unit 4) (mulPaid L.lows (addPaid (L.onePaid h unit 4)
    (by simpa only [Nat.mul_comm (2*K+4)] using mulPaid (2*K+4) source)))
  have write:=addPaid (addPaid (L.onePaid h unit 4) (mulPaid 10 folded))
    (addPaid (L.onePaid h unit 4) (by simpa only [Nat.mul_comm 54] using mulPaid 54 rowNum))
  have names:=mulPaid 7 (addPaid (L.onePaid h unit (15+L.lows*(11+4*K)))
    (addPaid (mulPaid 15 (addPaid folded (L.onePaid h unit 1))) (L.onePaid h unit 111)))
  have gather:=addPaid (addPaid scan write) names
  have pages:=mulPaid 2 (L.halfPaid h unit room.selection)
  have choice:=addPaid (addPaid (addPaid (L.onePaid h unit 4) (mulPaid 10 pages))
    (addPaid (L.onePaid h unit 4) (mulPaid L.blocks (addPaid (L.onePaid h unit 4)
      (by simpa only [Nat.mul_comm (2*25+4)] using mulPaid (2*25+4) target)))))
    (mulPaid 7 (addPaid (mulPaid 15 (addPaid pages (L.onePaid h unit 1))) (L.onePaid h unit (15+L.blocks*(11+4*25)))))
  simpa only [wordFactor,paid,literalFee,gatherFee,Shape.fee,DescentScalarBookReshape.cells, Paid, Nat.mul_one, K, DescentScalarHaloPortROM.length,
    DescentOrdinaryRefsROM.Chart.digitSize, DescentOrdinaryRefsROM.Chart.tableSize,
    DescentOrdinaryOriginReshape.Layout.rows, DescentOrdinaryOriginReshape.Layout.nextRows, Shape.rows,
    Layout.spread, Layout.join, Layout.prior, Layout.births, Layout.origins, Layout.durable, Layout.successors] using
    addPaid (addPaid (addPaid (addPaid (addPaid (addPaid (addPaid first second) third) port) refs) gather) choice) last

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI

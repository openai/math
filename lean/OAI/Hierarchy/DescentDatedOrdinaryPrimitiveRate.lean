import OAI.Hierarchy.DescentDatedPrimitiveExtent
import OAI.Hierarchy.DescentOrdinaryRoleRetileRate

namespace OAI
/-! Exponential address room for the physical primitive archive from the public scalar dimensions and LUT widths. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentOrdinaryPrimitiveCheckpoint DescentSIMDLookup Filter ProtocolRAM
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {ι : ℕ→Type*} {Pins : ∀h,ι h→Type} (v : ∀h (i:ι h),PhysicalOrdinary F (Pins h i))
local notation "L" h:arg i:arg => (v h i).paletteShape
local notation "B" h:arg i:arg => (v h i).bornBook

def primitivePeak (a : PhysicalOrdinary F P) :=
  let l:=a.paletteShape
  [DescentOperandFamilyBook.unit 1 a.bornBook.chipBits*a.bornBook.lanes,
    l.prior.bits*l.prior.beforeLanes,l.births.bits*l.births.beforeLanes,
    l.origins.bits*l.origins.beforeLanes,l.durable.bits*l.durable.beforeLanes,
    (l.references 0).digitBits,(l.references 0).width,l.spread.bits*l.spread.blocks*l.workLanes,
    l.join.width].foldr max 0

structure PrimitiveScalarRoom : Prop where
  hosts : Bounded (fun h i=>(L h i).hosts)
  groups : Bounded (fun h i=>(L h i).groups)
  lows : Bounded (fun h i=>(L h i).lows)
  blocks : Bounded (fun h i=>(L h i).blocks)
  ports : Bounded (fun h i=>(L h i).ports)
  cap : Bounded (fun h i=>(L h i).capacity)
  old : Bounded (fun h i=>(L h i).oldNodes)
  prior : Bounded (fun h i=>(L h i).priorLanes)
  birth : Bounded (fun h i=>(L h i).birthLanes)
  origin : Bounded (fun h i=>(L h i).originLanes)
  work : Bounded (fun h i=>(L h i).workLanes)
  next : Bounded (fun h i=>(L h i).nextLanes)
  donorHosts : Bounded (fun h i=>(B h i).hosts)
  donorGroups : Bounded (fun h i=>(B h i).groups)
  donorBlocks : Bounded (fun h i=>(B h i).blocks)
  donorCap : Bounded (fun h i=>(B h i).cap)
  packed : ∃C:ℕ,∀ᶠ h:ℕ in atTop,∀i,primitivePeak (v h i)≤C*h

private theorem chunkRate {g m : ∀h,ι h→ℕ} (hg : Bounded g) (hm : Bounded m) :
    Bounded (fun h i=>chunks (g h i) (m h i)) :=
  (hg.add hm).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)

set_option maxHeartbeats 850000 in
theorem primitive_rate (r : PrimitiveScalarRoom v) : Bounded (fun h i=>(v h i).primitiveRoof 0):=by
  obtain ⟨C,peak⟩:=r.packed
  have line (q : ∀h,ι h→ℕ) (hq : ∀h i,q h i≤primitivePeak (v h i)) :
      ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,q h i≤K*h :=
    ⟨C,peak.mono fun h hh i=>(hq h i).trans (hh i)⟩
  have tab (q : ∀h,ι h→ℕ) (hq : ∀h i,q h i≤primitivePeak (v h i)) :
      Bounded (fun h i=>2^(q h i)) :=by
    obtain ⟨k,hk⟩:=line q hq
    exact Bounded.pow_of_linear hk
  have one:=Bounded.const (ι:=ι) 1
  have two:=Bounded.const (ι:=ι) 2
  have zero:=Bounded.const (ι:=ι) 0
  have oldG:=r.groups.mul r.blocks
  have oldM:=r.work.mul r.blocks
  have newH:=r.hosts.mul r.lows
  have fieldCount:=(r.blocks.mul r.cap).mul (Bounded.const 6)
  have bornFields:=(r.donorBlocks.mul r.donorCap).mul (Bounded.const 6)
  have origins:=r.ports.mul r.blocks
  have N:=origins.mul (r.old.add (r.cap.mul (Bounded.const 6)))
  have oldRows:=r.hosts.mul (chunkRate oldG oldM)
  have rows:=r.hosts.mul (chunkRate r.groups r.work)
  have nextRows:=newH.mul (chunkRate r.groups r.work)
  have F0:=tab (fun h i=>DescentOperandFamilyBook.unit 1 (B h i).chipBits*(B h i).lanes) (by
    intro h i;simp [primitivePeak])
  have start : Bounded (fun h i=>(v h i).primitiveFirst 0):=by
    exact (zero.add ((one.add bornFields).mul (two.mul F0))).add
      (bornFields.mul (r.donorHosts.mul (chunkRate r.donorGroups r.birth)).padded)
  have s₁:=DescentOrdinaryRoleRetile.Layout.address_bound (fun h i=>(L h i).prior) _ r.hosts oldG r.prior oldM r.blocks start
    (line _ (by intro h i;simp [primitivePeak]))
  have s₂:=DescentOrdinaryRoleRetile.Layout.address_bound (fun h i=>(L h i).births) _ r.hosts oldG r.birth oldM fieldCount s₁
    (line _ (by intro h i;simp [primitivePeak]))
  have s₃:=DescentOrdinaryRoleRetile.Layout.address_bound (fun h i=>(L h i).origins) _ newH r.groups r.origin r.work r.blocks s₂
    (line _ (by intro h i;simp [primitivePeak]))
  have length:=(r.ports.mul oldRows).add (r.hosts.add (oldRows.add (r.hosts.mul r.ports)))
  have pad:=(((r.hosts.mul r.ports).max' (oldRows.max' r.hosts)).add one).padded
  have s₄:=(s₃.add length).add pad
  have digit:=tab (fun h i=>((L h i).references 0).digitBits) (by intro h i;simp [primitivePeak])
  have gates:=tab (fun h i=>((L h i).references 0).width) (by intro h i;simp [primitivePeak])
  have s₅:=(s₄.add (r.old.mul digit)).add (((Bounded.const 3).add N).mul two |>.mul gates)
  have raw:=r.lows.mul rows
  have tr:=(s₅.add raw.padded)
  have exp:=tab (fun h i=>(L h i).spread.bits*(L h i).spread.blocks*(L h i).workLanes)
    (by intro h i;simp [primitivePeak])
  have n:=r.blocks.mul nextRows
  have literal:=r.blocks.mul exp
  have main:=((tr.add (literal.add (two.mul n))).add (literal.add one).padded).add (n.add one).padded
  have s₆:=(main.add n).add nextRows.padded
  have jt:=tab (fun h i=>(L h i).join.width) (by intro h i;simp [primitivePeak])
  have s₇:=((s₆.add (two.mul jt)).add n).add (nextRows.add one).padded
  exact DescentOrdinaryRoleRetile.Layout.address_bound (fun h i=>(L h i).durable) _ newH r.groups r.work r.next r.blocks s₇
    (line _ (by intro h i;simp [primitivePeak]))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI

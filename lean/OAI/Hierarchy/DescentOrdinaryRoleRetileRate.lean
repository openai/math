import OAI.Hierarchy.DescentOrdinaryRoleRetile
import OAI.Hierarchy.DescentDatedOverlapAperture
import OAI.Hierarchy.DescentOrdinaryOverlapReserve

namespace OAI
/-! Shared roster conversion charges its one dictionary once across all physical panels. -/
namespace Hierarchy.DescentOrdinaryRoleRetile.Layout
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM DescentPackedZip DescentColonies.SplitRAM Filter DescentDatedAddressBook
noncomputable section
variable (L : Layout) (base : ℕ) (prior : Fin L.blocks→Bank) (w:ℕ)
set_option quotPrecheck false
local notation "P" => Overlap.pieces L.groups L.beforeLanes L.afterLanes
local notation "rows" => L.rows
local notation "K" => 1+40*P
local notation "out" => L.output base

theorem tariff :
    (phase L base prior w).ticks+7*names (phase L base prior w).program ≤
      327+115*(out-base)+L.blocks*((4+rows*(2*K+4))+7*(11+4*K)) :=by
  have work (i:ℕ) (hi:i<L.blocks) : (expr L base prior i).work≤K :=by
    simp only [expr,dite_eq_left hi]
    exact Overlap.body_work ..
  have code:=DescentOperandVectorArena.names_passes out rows rows w K (expr L base prior) 0
    (L.blocks) (fun i _ hi=>work i (by simpa using hi))
  have ticks:=DescentPackedFlowBatch.tariff out rows rows (L.blocks) (expr L base prior) K work
  have headers : names (Overlap.tables base L.hosts L.groups L.beforeLanes L.afterLanes (L.bits) w)=
      30+15*(out-base) :=by
    simp only [Overlap.tables,DescentOrdinaryAtomFieldRAM.ROM.mount,names_seq,names_mount,
      output,Overlap.dest,Overlap.dictBase,Nat.add_assoc,Nat.add_sub_cancel_left]
    omega
  change (8+10*(out-base)+clock (scans L base prior))+
    7*names ((Overlap.tables base L.hosts L.groups L.beforeLanes L.afterLanes (L.bits) w).seq
      (program w (scans L base prior)))≤_
  rw [names_seq,headers]
  calc
    _ ≤ ((8+10*(out-base))+(4+L.blocks*(4+rows*(2*K+4))))+
        7*((30+15*(out-base))+(15+L.blocks*(11+4*K))) := by dsimp only [scans] at *;omega
    _ = _ := by ring

def rowBill := (L.blocks+1)*((L.hosts*chunks L.groups L.beforeLanes)+L.rows+P+1)
def lookupBill := (P+1)*(L.beforeLanes+1)*2^(L.bits*L.beforeLanes)

theorem shared_fee (old : 0<L.beforeLanes) (next : 0<L.afterLanes) :
    (phase L base prior w).ticks+7*names (phase L base prior w).program ≤
      4096*(lookupBill L+rowBill L) := by
  let src : Bank:=⟨0,0⟩
  have headers : 115*(out-base) ≤ 2048*(lookupBill L+(L.hosts*chunks L.groups L.beforeLanes)+rows+1) := by
    apply le_trans _ (Overlap.tariff base L.hosts L.groups L.beforeLanes L.afterLanes (L.bits) w src old next)
    simp only [Overlap.program,Overlap.tables,DescentOrdinaryAtomFieldRAM.ROM.mount,names_seq,names_mount,names_scan,
      Overlap.ticks,output,Overlap.dest,Overlap.dictBase,Nat.add_assoc,Nat.add_sub_cancel_left]
    omega
  have probes : rows*P≤2*((L.hosts*chunks L.groups L.beforeLanes)+rows) := by
    have b:=Nat.mul_le_mul_left L.hosts (Overlap.probes (G:=L.groups) old next)
    change L.hosts*chunks L.groups L.afterLanes*P≤2*(L.hosts*chunks L.groups L.beforeLanes+L.hosts*chunks L.groups L.afterLanes)
    unfold Overlap.pieces
    nlinarith only [b]
  have each : (4+rows*(2*K+4))+7*(11+4*K)≤2048*((L.hosts*chunks L.groups L.beforeLanes)+rows+P+1) := by nlinarith only [probes]
  let rowCost:=(L.hosts*chunks L.groups L.beforeLanes)+rows+P+1
  have startup : 327+115*(out-base)≤4096*(lookupBill L+rowCost) :=by
    dsimp only [rowCost]
    omega
  have perBlock : (4+rows*(2*K+4))+7*(11+4*K)≤4096*rowCost :=
    each.trans (Nat.mul_le_mul_right rowCost (by decide : 2048≤4096))
  apply (tariff L base prior w).trans
  calc
    _ ≤ 4096*(lookupBill L+rowCost)+L.blocks*(4096*rowCost) :=
      Nat.add_le_add startup (Nat.mul_le_mul_left L.blocks perBlock)
    _ = _ :=by
      change _=4096*(lookupBill L+(L.blocks+1)*rowCost)
      ring

/-- The table is bought once. The rest of the measured native time is linear in the
two authentic packed row counts even for unrelated lane counts and nonempty tail rows. -/
theorem cofinal_fee (factor saving : ℕ) :
    ∀ᶠ h:ℕ in atTop,∀(L : Layout) (base w J original : ℕ) (prior : Fin L.blocks→Bank),
      J≤Nat.log 2 h → 2^h≤original → 0<L.beforeLanes → 0<L.afterLanes → L.beforeLanes≤h → L.afterLanes≤h →
      L.bits*L.beforeLanes≤h/2 → w+1≤factor*h →
      ((phase L base prior w).ticks+7*names (phase L base prior w).program)*(w+1)
        ≤original/(2^J)^saving+4096*(rowBill L)*(factor*h) :=by
  filter_upwards [Overlap.charged_half_pages (4096*factor) 1 0 saving] with h gates
  intro L base w J original prior small large old next a b packed arch
  have half:=Overlap.half_pages h L.groups L.beforeLanes L.afterLanes (L.bits) a b packed
  have smallFee:=gates J 0 original small (by simp) large
  have page : 4096*(lookupBill L)*(factor*h)≤original/(2^J)^saving :=by
    apply le_trans _ smallFee
    change 4096*((Overlap.pieces L.groups L.beforeLanes L.afterLanes+1)*(L.beforeLanes+1)*2^(L.bits*L.beforeLanes))*(factor*h)≤_
    simp only [pow_zero,Nat.mul_one]
    nlinarith only [Nat.mul_le_mul_left (4096*factor*h) half]
  calc
    _ ≤ (4096*(lookupBill L+rowBill L))*(factor*h) :=
      Nat.mul_le_mul (shared_fee L base prior w old next) arch
    _ = 4096*(lookupBill L)*(factor*h)+4096*(rowBill L)*(factor*h) := by ring
    _ ≤ _ := Nat.add_le_add_right page _

open DescentDatedAddressBook

theorem address_bound {ι : ℕ→Type*} (L : ∀h,ι h→DescentOrdinaryRoleRetile.Layout)
    (base : ∀h,ι h→ℕ) (hosts : Bounded (fun h i=>(L h i).hosts)) (groups : Bounded (fun h i=>(L h i).groups))
    (old : Bounded (fun h i=>(L h i).beforeLanes)) (nxt : Bounded (fun h i=>(L h i).afterLanes))
    (count : Bounded (fun h i=>(L h i).blocks)) (origin : Bounded base)
    (packed : ∃k:ℕ,∀ᶠ h:ℕ in Filter.atTop,∀i,(L h i).bits*(L h i).beforeLanes≤k*h) :
    Bounded (fun h i=>(L h i).roof (base h i)) :=by
  have sec_:=Overlap.address_rate (a:=fun h i=>(L h i).bits) hosts groups old nxt packed
  have grid : Bounded (fun h i=>chunks (L h i).groups (L h i).afterLanes) :=
    (groups.add nxt).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have raw : Bounded (fun h i=>(L h i).rows) := hosts.mul grid
  apply ((origin.add sec_).add (count.mul raw)).of_le
  intro h i
  rw [translated]
  apply le_of_eq
  change base h i+((L h i).output 0+(L h i).blocks*(L h i).rows+2^Nat.clog 2 ((L h i).rows+1))=
    (base h i+((L h i).output 0+2^Nat.clog 2 ((L h i).rows+1)))+(L h i).blocks*(L h i).rows
  ac_rfl

end
end Hierarchy.DescentOrdinaryRoleRetile.Layout

end OAI

import OAI.Hierarchy.DescentResetRosterFunctions
import OAI.Hierarchy.DescentClosedRosterCoverage
import OAI.Hierarchy.DescentPackedFallbackAllowance
import OAI.Hierarchy.DescentResetSignedScan
import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! # The full five-family packed public reset prefix and its genuine candidate count -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentResetLocalRoster DescentSIMDLookup
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "height" => GroupStage.depthBound D n f g
local notation "budget" => S.epochPower^(S.fallbackExponent cut)

theorem local_roster_exact :
    totalLocal B=publicSlots ctl.board height k input.placement.cap := by
  rw [←same_slots B.reset.graph ctl.board B.dimension B.graph height k input.placement.cap]
  unfold totalLocal stemsCount contactCount privateCount publicSlots
  simp only [B.keyWidth,B.commonDepth,Nat.add_sub_cancel_left,DescentResetCableSlots.cableCap]

/-- Every tagged history reaching this public date executes the same number of
candidate iterations. The initial cap and the capacity factors determine the date. -/
theorem local_roster_calendar {W₀ W₂ : MarkedWorld F d P bits} {z₀ D₀ j z₂ D₂ : ℕ}
    {first : Reached W₀ G q ε S k 0 z₀ D₀ w hist} {last : Reached W₂ G q ε S k j z₂ D₂ w hist}
    (a : Chronology.Path first input) (b : Chronology.Path input last)
    (calendar : List ℕ) (issued : (a.append b).capFactors=calendar) (cap₀ : first.placement.cap=256) :
    totalLocal B=publicSlots ctl.board height k ((calendar.take i).prod*256) := by
  rw [local_roster_exact B,a.capacity_prefix b calendar issued,cap₀,Nat.sub_zero]

/-- Includes unused paid reservations and both orientations in the concrete local injection.
All fixed constants only use the selected graph and the public reset height. -/
theorem local_roster_paid :
    totalLocal B ≤ rosterFactor ctl.board height*budget := by
  have cutoff : B.reset.k-B.terminals.commonDepth=k:=by rw [B.keyWidth,B.commonDepth];omega
  have slots : 2^k*(2*input.placement.cap)≤budget:=by
    simpa only [ClosedReset.fallbackSlots,cutoff] using B.fallbackSlots_paid B.age.le
  have single:=S.fallback_slots (cap:=1) ctl.height B.age.le
    (Nat.two_pow_pos _ : 1≤2^(8+S.capGain*i)) ctl.fixed
  have block : 2^k≤budget := (Nat.le_mul_of_pos_right _ (by decide : 0<2*1)).trans single
  have large : 0<budget := pow_pos (Nat.two_pow_pos _) _
  let Y:=2^B.reset.n
  let Q:=DescentResetCableSlots.cableCap B.reset.graph height
  have aux:=Nat.mul_le_mul_left (4*(Y+2)*(Y+2^height+Q)) block
  rw [←same_factor B.reset.graph ctl.board B.dimension B.graph height]
  change _≤(3+4*(Y+2)*(Y+2^height+Q))*budget
  unfold totalLocal stemsCount contactCount privateCount rootSlots
  simp only [B.keyWidth,B.commonDepth,Nat.add_sub_cancel_left,pow_succ]
  change 2*(2^k*(2*input.placement.cap))+
    (1+(2*((2^k*2+2^k*2*(Y+1))*(Y+2^height))+
      2*((2^k*2+2^k*2*(Y+1))*Q)))≤_
  nlinarith only [slots,block,large,aux]

theorem local_roster_power :
    totalLocal B≤S.epochPower^(S.fallbackExponent cut+Nat.clog 2 (rosterFactor ctl.board height)) := by
  let fixed:=rosterFactor ctl.board height
  have two : 2≤S.epochPower:=Nat.one_lt_two_pow ctl.height.ne'
  have room : fixed≤S.epochPower^(Nat.clog 2 fixed):=
    (Nat.le_pow_clog (by decide) fixed).trans (Nat.pow_le_pow_left two _)
  rw [pow_add,Nat.mul_comm]
  exact (local_roster_paid B).trans (Nat.mul_le_mul_right _ room)

/-- The lookup-table exponent used by the actual streaming comparator is independent
of the number of candidate rows. -/
theorem prefix_lane_room (hdata b unit : ℕ) (price : 10*b≤unit) :
    (10*b)*lanes hdata unit≤hdata/2 := by
  calc
    (10*b)*lanes hdata unit ≤ unit*lanes hdata unit := Nat.mul_le_mul_right _ price
    _ = _ := Nat.mul_comm _ _
    _ ≤ _ := lanes_fit ..

/-- The original native sum reads every packed candidate once. It includes both sampled
input expressions, the two mounted lookup pages, and seven instruction words per name. -/
theorem prefix_issued_price (H groups payload word unit ratio span bound : ℕ) (unitPos : 0<unit)
    (wide : 2*unit≤payload) (cpu : word≤ratio*payload) (tables : span≤payload/2)
    (table : DescentPackedZip.Tables) (query : ProtocolRAM.Expr) (row : Fin (totalLocal B)→ProtocolRAM.Expr)
    (queryWork : query.work≤bound) (rowWork : ∀j,(row j).work≤bound) :
    let N:=H*chunks groups (lanes payload unit)
    let op:=DescentColonies.SplitRAM.total (fun j=>table.read query (row j)) (List.finRange (totalLocal B))
    let clocks:=(4+10*(2*2^span))+(4+N*(2*op.work+4))
    let names:=15*(2*2^span+1)+(11+4*op.work)
    (clocks+7*names)*word ≤
      1024*ratio*(2^(payload/2)*payload)+
      1024*ratio*(1+rosterFactor ctl.board height*budget)*(bound+1)*
        (payload+H*payload+4*H*groups*unit) := by
  intro N op clocks names
  let K:=rosterFactor ctl.board height*budget
  have count : totalLocal B≤K:=local_roster_paid B
  have weight (j : Fin (totalLocal B)) : (table.read query (row j)).work≤2*bound+11:=by
    rw [DescentPackedZip.work];have :=rowWork j;omega
  have sum:=DescentColonies.SplitRAM.work_total _ _ weight (List.finRange (totalLocal B))
  simp only [List.length_finRange] at sum
  have term : op.work≤24*(K+1)*(bound+1):=by
    exact sum.trans (by nlinarith only [Nat.mul_le_mul_right (2*bound+11+1) count,Nat.zero_le (K*bound),Nat.zero_le bound,Nat.zero_le K])
  have volume:=DescentSIMDLookup.volume H groups payload unit unitPos wide
  have pages : 2^span≤2^(payload/2):=Nat.pow_le_pow_right (by decide) tables
  let V := H*payload+4*H*groups*unit
  let R := (1+K)*(bound+1)
  let U := 2^(payload/2)*(ratio*payload)
  have packed : N*word ≤ ratio*V := by
    change N*payload ≤ V at volume
    exact (Nat.mul_le_mul_left N cpu).trans (by
      simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left ratio volume)
  have room : 1 ≤ R := Nat.mul_pos (by omega) (by omega)
  have payloadRoom : payload ≤ payload+V := Nat.le_add_right ..
  have volRoom : V ≤ payload+V := Nat.le_add_left ..
  have fixed := Nat.mul_le_mul term cpu
  have batch := Nat.mul_le_mul term packed
  have scale : 24*(K+1)*(bound+1)=24*R := by dsimp [R]; ring
  rw [scale] at fixed batch
  have fixedBound : op.work*word ≤ 24*(R*ratio*(payload+V)) := fixed.trans (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (24*R*ratio) payloadRoom)
  have batchBound : op.work*(N*word) ≤ 24*(R*ratio*(payload+V)) := batch.trans (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (24*R*ratio) volRoom)
  have idleBound : N*word ≤ R*ratio*(payload+V) := packed.trans (by
    calc
      ratio*V ≤ ratio*(payload+V) := Nat.mul_le_mul_left _ volRoom
      _ ≤ R*(ratio*(payload+V)) := Nat.le_mul_of_pos_left _ room
      _ = _ := (Nat.mul_assoc ..).symm)
  have pageBound : 2^span*word ≤ U := Nat.mul_le_mul pages cpu
  have wordBound : word ≤ U := cpu.trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  calc
    (clocks+7*names)*word =
        190*word+230*(2^span*word)+2*(op.work*(N*word))+4*(N*word)+28*(op.work*word) := by
          dsimp only [clocks,names]
          ring
    _ ≤ 1024*U+1024*(R*ratio*(payload+V)) := by omega
    _ = _ := by dsimp [U,R,V,K]; ring

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

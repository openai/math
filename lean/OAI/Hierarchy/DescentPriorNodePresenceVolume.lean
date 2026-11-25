import OAI.Hierarchy.DescentPriorNodePresenceShape
import OAI.Hierarchy.DescentOrdinaryRoleRetileRate
import OAI.Hierarchy.DescentOrdinaryOverlapReserve
import OAI.Hierarchy.DescentRetainedMovementBits
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! The original role-to-node census uses separate pitches for its archived role
tokens and its retained operands. Both scans run over the padded host set. -/
namespace Hierarchy.DescentPriorNodePresence.Chart
open DescentSIMDLookup DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

def areaFee (c : Chart) :=
  let before:=c.hosts*chunks c.groups c.roleLanes
  let after:=c.hosts*chunks c.groups c.operandLanes
  8192*(2^((c.tokenBits*c.nodes)*c.roleLanes)+2^(c.nodes*c.operandLanes)+
    c.convert.lookupBill+c.convert.rowBill+(c.blocks+1)*(before+1)+(2*c.blocks+1)*(after+1))

theorem area_bound (c : Chart) (h : ℕ) (old : c.roleLanes ≤ h) (new : c.operandLanes ≤ h)
    (source : c.tokenBits*c.nodes*c.roleLanes ≤ h/2) (mask : c.nodes*c.roleLanes ≤ h/2)
    (target : c.nodes*c.operandLanes ≤ h/2) (hosts : 0 < c.hosts) :
    let before:=c.hosts*chunks c.groups c.roleLanes
    let after:=c.hosts*chunks c.groups c.operandLanes
    c.areaFee ≤ 65536*(c.blocks+1)*(before+after+1)+32768*(h+1)^2*2^(h/2) := by
  intro before after
  let shards:=Overlap.pieces c.groups c.roleLanes c.operandLanes
  have pieces:shards ≤ before:=(Nat.min_le_left ..).trans (Nat.le_mul_of_pos_left _ hosts)
  have bk:=Overlap.half_pages h c.groups c.roleLanes c.operandLanes c.nodes old new mask
  have book:c.convert.lookupBill ≤ 2*(h+1)^2*2^(h/2):=by
    simpa only [DescentOrdinaryRoleRetile.Layout.lookupBill,convert,one_mul] using bk
  have rows:c.convert.rowBill ≤ (c.blocks+1)*(2*before+after+1):=by
    change (c.blocks+1)*(before+after+shards+1) ≤ _
    exact Nat.mul_le_mul_left _ (by omega)
  have inTable:=Nat.pow_le_pow_right (by decide : 0<2) source
  have outTable:=Nat.pow_le_pow_right (by decide : 0<2) target
  have one : 1 ≤ (h+1)^2:=Nat.pow_pos (Nat.succ_pos _)
  have size:=Nat.mul_le_mul_right (2^(h/2)) one
  change 8192*(_+_+_+_+(c.blocks+1)*(before+1)+(2*c.blocks+1)*(after+1)) ≤ _
  nlinarith only [book,rows,inTable,outTable,size,Nat.zero_le (c.blocks*before),Nat.zero_le (c.blocks*after),
    Nat.zero_le c.blocks,Nat.zero_le before,Nat.zero_le after]

theorem cofinal_area (ratio rate saving : ℕ) : ∀ᶠ h : ℕ in atTop,∀(c : Chart) (J copies w u δ : ℕ),
    0 < c.hosts → 0 < δ → c.blocks ≤ scale J rate → u ≤ scale J rate →
    0 < c.roleLanes → 0 < c.operandLanes → c.roleLanes ≤ h → c.operandLanes ≤ h →
    c.tokenBits*c.nodes*c.roleLanes ≤ h/2 → c.nodes*c.roleLanes ≤ h/2 → c.nodes*c.operandLanes ≤ h/2 →
    (c.groups ≤ c.roleLanes ∨ h ≤ c.roleLanes*u) → (c.groups ≤ c.operandLanes ∨ h ≤ c.operandLanes*u) →
    J ≤ Nat.log 2 h → 2^h ≤ copies → w ≤ ratio*h →
    let unit:=524288*(ratio+1)*scale J (2*rate)
    c.areaFee*w ≤ c.hosts*h*unit+c.hosts*(c.groups*δ)*unit+copies/(2^J)^saving :=by
  filter_upwards [global_control_shared (32768*ratio) 3 0 1 saving] with h quote
  intro c J copies w u δ hosts stages blocks density old new oldFit newFit src mask dst from_ to_ age ambient cpu unit
  let before:=c.hosts*chunks c.groups c.roleLanes
  let after:=c.hosts*chunks c.groups c.operandLanes
  let U:=scale J rate
  have pos:1 ≤ U:=Nat.two_pow_pos _
  have square:U*U=scale J (2*rate):=by rw [scale_mul,two_mul]
  have grow:U ≤ U*U:=Nat.le_mul_of_pos_right _ pos
  have each : c.blocks+1 ≤ 2*U:=by omega
  have counted:=area_bound c h oldFit newFit src mask dst hosts
  have original : before*h ≤ c.hosts*h+c.hosts*c.groups*u:=
    DescentResetRetainedSetup.Layout.bounded_pitch_rows old from_
  have output : after*h ≤ c.hosts*h+c.hosts*c.groups*u:=
    DescentResetRetainedSetup.Layout.bounded_pitch_rows new to_
  have ratioH : h ≤ c.hosts*h:=Nat.le_mul_of_pos_left _ hosts
  have group : c.hosts*c.groups ≤ c.hosts*(c.groups*δ):=Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ stages)
  have row : (before+after+1)*h ≤ 3*(c.hosts*h)+2*(c.hosts*(c.groups*δ))*U:=by
    have indexed:=Nat.mul_le_mul group density
    nlinarith only [original,output,ratioH,indexed]
  have growRatio:ratio*U ≤ (ratio+1)*(U*U):=Nat.mul_le_mul (Nat.le_succ _) grow
  have sameRatio:ratio*(U*U) ≤ (ratio+1)*(U*U):=Nat.mul_le_mul_right _ (Nat.le_succ ratio)
  have variableCost : (65536*(c.blocks+1)*(before+after+1))*(ratio*h) ≤
      c.hosts*h*unit+c.hosts*(c.groups*δ)*unit:=by
    dsimp only [unit]
    rw [←square]
    have scaled:=Nat.mul_le_mul each row
    nlinarith only [Nat.mul_le_mul_left (65536*ratio) scaled, Nat.mul_le_mul_left (c.hosts*h) growRatio,
      Nat.mul_le_mul_left (c.hosts*(c.groups*δ)) sameRatio,
      Nat.zero_le ((c.hosts*h)*((ratio+1)*(U*U))),
      Nat.zero_le ((c.hosts*(c.groups*δ))*((ratio+1)*(U*U)))]
  have global:=quote J 0 copies age (by simp) ambient
  simp only [pow_zero,mul_one] at global
  have table : 32768*(h+1)^2*2^(h/2)*(ratio*h) ≤ copies/(2^J)^saving:=by
    apply le_trans _ global
    nlinarith only [Nat.zero_le (ratio*(h+1)^2*2^(h/2))]
  have total:=Nat.mul_le_mul counted cpu
  exact total.trans (by rw [Nat.add_mul];exact Nat.add_le_add variableCost table)

end
end Hierarchy.DescentPriorNodePresence.Chart

end OAI

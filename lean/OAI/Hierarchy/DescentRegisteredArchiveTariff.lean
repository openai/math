import OAI.Hierarchy.DescentPaddedResetCharges
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! The two prior archive rectangles, including newly initialized host rows,
are charged against the original old hosts and their groups. -/
namespace Hierarchy.DescentResetPriorHostPad.Shape
open DescentCompiler.TerminalScale
noncomputable section

theorem volume_paid (s : Shape) (h J rate ratio δ args token : ℕ)
    (old : 0 < s.newHosts) (radix : 0 < δ) (arity : s.arguments ≤ scale J rate)
    (blocks : s.blocks ≤ scale J rate) (argument : args ≤ scale J rate) (roles : token ≤ scale J rate) :
    ratio*s.volume h args token ≤ s.newHosts*h*(16384*(ratio+1)*scale J (3*rate))+
      s.newHosts*(s.groups*δ)*(16384*(ratio+1)*scale J (3*rate)) := by
  let L:=scale J rate
  have pos:1 ≤ L:=Nat.two_pow_pos _
  have square:L ≤ L*L:=Nat.le_mul_of_pos_right _ pos
  have cube:L*L ≤ L*L*L:=Nat.le_mul_of_pos_right _ pos
  have form:L*L*L=scale J (3*rate):=by
    dsimp [L]
    rw [scale_mul,scale_mul]
    congr 1
    omega
  have pages:s.dataRect.pages+1 ≤ 10*(L*L):=by
    change (2+7*s.arguments)*s.blocks+1 ≤ _
    have mul:=Nat.mul_le_mul (show 2+7*s.arguments ≤ 9*L by omega) blocks
    nlinarith only [mul,pos,square]
  have sockets:s.blocks+1 ≤ 2*(L*L):=by omega
  have host:s.newHosts+1 ≤ 2*s.newHosts:=by omega
  have target:s.newHosts*s.groups ≤ s.newHosts*(s.groups*δ):=Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ radix)
  let rect:=2*(s.newHosts*h)+(s.newHosts*(s.groups*δ))*L
  have row (z : ℕ) (width : z ≤ L) : (s.newHosts+1)*h+s.newHosts*s.groups*z ≤ rect:=by
    have heads:=Nat.mul_le_mul_right h host
    have indexed:=Nat.mul_le_mul target width
    dsimp only [rect]
    nlinarith only [heads,indexed]
  have first:=Nat.mul_le_mul (Nat.mul_le_mul_left 512 pages) (row args argument)
  have second:=Nat.mul_le_mul (Nat.mul_le_mul_left 512 sockets) (row token roles)
  have paid:s.volume h args token ≤ 6144*(L*L)*rect:=by
    unfold volume
    nlinarith only [first,second]
  apply (Nat.mul_le_mul_left ratio paid).trans
  rw [←form]
  dsimp only [rect]
  have cheap:ratio*(L*L) ≤ (ratio+1)*(L*L*L):=Nat.mul_le_mul (Nat.le_succ _) cube
  have groups:ratio*(L*L*L) ≤ (ratio+1)*(L*L*L):=Nat.mul_le_mul_right _ (Nat.le_succ ratio)
  calc
    _ = s.newHosts*h*(12288*(ratio*(L*L))) + s.newHosts*(s.groups*δ)*(6144*(ratio*(L*L*L))) := by ring
    _ ≤ _ := by
      apply Nat.add_le_add <;> apply Nat.mul_le_mul_left
      · simpa only [Nat.mul_assoc] using Nat.mul_le_mul (by decide : 12288 ≤ 16384) cheap
      · simpa only [Nat.mul_assoc] using Nat.mul_le_mul (by decide : 6144 ≤ 16384) groups

end
end Hierarchy.DescentResetPriorHostPad.Shape

namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentCompiler.TerminalScale
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ) (prev : DatePorts) (floor w : ℕ)
local notation "raw" => previousArchiveLayout G S board k tail age p f g drift degree h ordinary op s Z prev floor

theorem archive_rectangles (J rate ratio args token : ℕ)
    (o : 0 < prev.operandLanes) (r : 0 < prev.roleLanes) (old : 0 < prev.venue.hosts)
    (radix : 0 < S.radix) (items : prev.venue.groups ≤ prev.operandLanes ∨ h ≤ prev.operandLanes*args)
    (signals : prev.venue.groups ≤ prev.roleLanes ∨ h ≤ prev.roleLanes*token)
    (bus : w ≤ ratio*h) (arity : prev.argumentsPerNode ≤ scale J rate) (blocks : 2^k ≤ scale J rate)
    (arg : args ≤ scale J rate) (role : token ≤ scale J rate) :
    let phase:=(prev.resetPad k).phase floor (prev.archive.prior raw) (fun x=>prev.archive.roles.bank x.val) w
    (phase.ticks+7*DescentStaticWordColumn.names phase.program)*w ≤
      prev.venue.hosts*h*(16384*(ratio+1)*scale J (3*rate))+
      prev.venue.hosts*(prev.venue.groups*S.radix)*(16384*(ratio+1)*scale J (3*rate)) :=by
  let pad:=prev.resetPad k
  have native:=pad.word_bill floor w h ratio args token (prev.archive.prior raw) (fun x=>prev.archive.roles.bank x.val)
    o r items signals bus
  exact native.trans (pad.volume_paid h J rate ratio S.radix args token old radix arity blocks arg role)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI

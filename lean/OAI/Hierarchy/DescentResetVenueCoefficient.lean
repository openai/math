import OAI.Hierarchy.DescentResetOutgoingVenueBill
import OAI.Hierarchy.DescentResetReceiptControls

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler TerminalScale DescentSixParty DescentVenueQuantityPlanes DescentDenseHostOrder
noncomputable section
set_option quotPrecheck false

def rosterWeight (n d Ht : ℕ) := 4*((2^n+1)+((2*d+4)*2^n+(2^n+1)*2^(Ht+1)))

def venueLead (n d D f g : ℕ) :=
  (4*resetPlaneFactor 1+DescentCompactVenuePeers.compactFactor+4096*(2*2^g+8)+
   1024*6+115)*(12*(rosterWeight n d (GroupStage.depthBound D n f g)+2))

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "v" => (fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base).venue
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "growth" => 2^S.hostGain*S.radix

theorem original_venue_coefficient (D J rate : ℕ) (branch : prior.venue.degree=D) (blocks : prior.venue.k=k)
    (window : 2^k ≤ scale J rate) (capacity : cap ≤ scale J rate) (gain : growth ≤ scale J rate) :
    venueFactor (v) growth ≤ venueLead n d D f g*scale J (3*rate) := by
  let u:=scale J rate
  let A:=2^g
  let N:=2^k
  let C₀:=4*resetPlaneFactor 1+DescentCompactVenuePeers.compactFactor+4096*(2*A+8)+1024*6+115
  let r:=rosterWeight n d (GroupStage.depthBound D n f g)
  have one:1 ≤ u:=Nat.two_pow_pos _
  have twice:u ≤ u*u:=Nat.le_mul_of_pos_right u one
  have product:N*cap ≤ u*u:=Nat.mul_le_mul window capacity
  have seats:(v).dense.shapes ≤ r*u:=by
    change (roster board k (GroupStage.depthBound prior.venue.degree n f g)).card ≤ _
    rw [branch]
    have actual:=roster_bound board k (GroupStage.depthBound D n f g)
    rw [pow_succ 2 k] at actual
    refine actual.trans ?_
    calc
      _ = r*N:=by dsimp only [r,rosterWeight,N];ring
      _ ≤ _:=Nat.mul_le_mul_left _ window
  have ports:(v).next.resetFactor ≤ (4096*(2*A+8)+1024*6+115)*(u*u):=by
    change 4096*((2^prior.venue.k*(2*(A*cap))+2)+2*(2^prior.venue.k+2))+
      1024*(2^prior.venue.k+3+1)+115*2^prior.venue.k ≤ _
    rw [blocks]
    change 4096*((N*(2*(A*cap))+2)+2*(N+2))+1024*(N+3+1)+115*N ≤ _
    have bounded : N ≤ u := window
    nlinarith only [one,twice,bounded,Nat.mul_le_mul_left (2*A) product,Nat.zero_le (u*u)]
  have setup:2*resetPlaneFactor 1*((v).dense.blocks+1)+DescentCompactVenuePeers.compactFactor+(v).next.resetFactor ≤ C₀*(u*u):=by
    change 2*resetPlaneFactor 1*(N+1)+_+_ ≤ _
    dsimp only [C₀]
    have old: N+1 ≤ 2*(u*u):=by omega
    have constant:DescentCompactVenuePeers.compactFactor ≤ DescentCompactVenuePeers.compactFactor*(u*u):=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos one one)
    nlinarith only [ports,constant,Nat.mul_le_mul_left (2*resetPlaneFactor 1) old]
  have localSlots:12*((v).dense.shapes+growth+1) ≤ 12*(r+2)*u:=by
    nlinarith only [seats,gain,one]
  calc
    _ ≤ (C₀*(u*u))*(12*(r+2)*u):=Nat.mul_le_mul setup localSlots
    _ = venueLead n d D f g*(u*u*u):=by dsimp only [C₀,r,A,venueLead];ring
    _ = _:=by
      congr 1
      dsimp only [u,scale]
      rw [←pow_add,←pow_add]
      congr 1
      ring

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

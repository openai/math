import OAI.Hierarchy.DescentRetainedScaledFee
import OAI.Hierarchy.DescentOrdinarySharedLedger

namespace OAI
/-! # The two packed host layouts pay for one reset on the shared calendar -/
namespace Hierarchy.DescentRetainedSeven.Chart
open DescentCompiler DescentCompiler.TerminalScale DescentResetRetainedSetup Filter
noncomputable section
variable (c : Chart)
local notation "L" => c.retained
local notation "P" => c.placement

def hostRate (growth : ℕ) :=10+(P).blocks+growth
def fieldRate (growth oldUnit u packet next : ℕ) :=oldUnit+112*u+packet+(1+growth)*next

private theorem residue (h : ℕ) :
    (Layout.halfLiteral h+1)*h+(h+1)^3*2^(h/2)*h+h≤5*(h+1)^4*2^(h/2) :=by
  let page:=2^(h/2)
  have four : (h+1)^3*(h+1)=(h+1)^4:=by ring
  have a : (h+1)^2*h≤(h+1)^4:=(Nat.mul_le_mul
    (Nat.pow_le_pow_right (Nat.succ_pos h) (by decide : 2≤3)) (Nat.le_succ h)).trans_eq four
  have b : (h+1)^3*h≤(h+1)^4:=(Nat.mul_le_mul_left _ (Nat.le_succ h)).trans_eq four
  have ab:=Nat.mul_le_mul_right page a
  have bb:=Nat.mul_le_mul_right page b
  have j : h≤(h+1)^4:=(Nat.le_succ h).trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos h) (by decide : 1≤4))
  have term : h≤(h+1)^4*page:=j.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  change (2*(h+1)^2*page+1)*h+(h+1)^3*page*h+h≤5*(h+1)^4*page
  nlinarith only [ab,bb,term]

theorem row_invoice (h growth oldUnit u packet next : ℕ)
    (hosts : (P).newHosts≤(L).hosts*growth) (groups : (P).groups≤(L).groups) :
    c.rowBits h oldUnit u packet next≤
      (L).hosts*h*c.hostRate growth+(L).hosts*(L).groups*fieldRate growth oldUnit u packet next+
        5*(h+1)^4*2^(h/2) :=by
  let H:=(L).hosts
  let G:=(L).groups
  calc
    _ ≤ (Layout.halfLiteral h+1)*h + 6*(H*h)+H*G*(oldUnit+5*(16*u))+
        (H*(P).blocks*h+H*G*packet)+(H*h+H*G*(16*u))+(H*h+H*G*(16*u))+
        (H*h+H*G*next)+H*h+(H*growth*h+(H*growth)*G*next)+(h+1)^3*2^(h/2)*h+h := by
        unfold rowBits;dsimp only [H,G];gcongr
    _ = H*h*c.hostRate growth+H*G*fieldRate growth oldUnit u packet next+
        ((Layout.halfLiteral h+1)*h+(h+1)^3*2^(h/2)*h+h) :=by unfold hostRate fieldRate;ring
    _ ≤ _ :=Nat.add_le_add_left (residue h) _

/-- This is the pointwise bound consumed by the schedule ledger. Only the
literal lookup pages require the original-site shared allowance. -/
theorem shared_receipt (r saving : ℕ) :
    ∀ᶠ h:ℕ in atTop,∀ (c : Chart) (J original K growth old u packet next cost : ℕ),
      J≤Nat.log 2 h → 2^h≤original → K≤ scale J r →
      c.placement.newHosts≤c.retained.hosts*growth → c.placement.groups≤c.retained.groups →
      cost≤K*c.rowBits h old u packet next →
      cost≤c.retained.hosts*h*(K*c.hostRate growth)+c.retained.hosts*c.retained.groups*(K*fieldRate growth old u packet next)+original/(2^J)^saving :=by
  filter_upwards [global_control_shared 5 4 r 1 saving] with h paid
  intro c J original K growth old u packet next cost late ambient rate host grp native
  have shared := paid J (r*(J+1)) original late (by simp) ambient
  have roof:=c.row_invoice h growth old u packet next host grp
  have lit : K*(5*(h+1)^4*2^(h/2))≤original/(2^J)^saving :=calc
    _ ≤ scale J r*(5*(h+1)^4*2^(h/2)):=Nat.mul_le_mul_right _ rate
    _ = (5*(h+1)^4*2^(r*(J+1)))*2^(h/2):=by unfold scale;ring
    _ ≤ _:=shared
  apply native.trans ((Nat.mul_le_mul_left K roof).trans ?_)
  calc
    _ = c.retained.hosts*h*(K*c.hostRate growth)+c.retained.hosts*c.retained.groups*(K*fieldRate growth old u packet next)+K*(5*(h+1)^4*2^(h/2)):=by ring
    _ ≤ _:=Nat.add_le_add_left lit _

end
end Hierarchy.DescentRetainedSeven.Chart

end OAI

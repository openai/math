import OAI.Hierarchy.DescentPhysicalFundingPrice
import OAI.Hierarchy.DescentResetRootPitchRows
import OAI.Hierarchy.DescentNamedResetOutput

namespace OAI
/-! The physical funding chart at the preceding host order and both actual lane widths. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentSIMDLookup DescentCompiler DescentCompiler.TerminalScale DescentGLNielsen
open PhysicalReset.FinalInputs
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "v" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "s" => (v).funded
local notation "t" => (v).venue.census
local notation "cc" => S.groupWidth k tail age

theorem funded_pitch (groups : prior.venue.groups=2^cc) (low : e≤cc) :
    2^(s).high≤chunks (s).oldGroups (s).gatherLanes ∧
      (t).rows=(s).hosts*chunks (s).oldGroups (s).gatherLanes:=by
  change 2^(cc-e)≤chunks prior.venue.groups (2^e) ∧
    prior.venue.hosts*chunks (2^cc) (2^e)=prior.venue.hosts*chunks prior.venue.groups (2^e)
  rw [groups,dyadic_chunks cc e low]
  exact ⟨le_rfl,rfl⟩

theorem funding_factor_local (J rate : ℕ) (low : e≤cc)
    (blocks : 2^prior.venue.k≤ scale J rate)
    (dim : cc+k≤ scale J rate) (sites : (t).jobs≤ scale J rate) (cap : prior.venue.cap≤ scale J rate) :
    fundingFactor (s) (t)≤2000000*scale J (2*rate):=by
  let L:=scale J rate
  have one:1≤L:=Nat.two_pow_pos _
  have ll:L≤L*L:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right L one
  have two:1≤L*L:=one.trans ll
  have room:(s).high+(s).low=cc+k:=by change cc-e+(e+k)=cc+k;omega
  have sched:=DescentGLNielsen.length_le ((s).high+(s).low)
  rw [room] at sched
  have square:=(Nat.mul_le_mul dim dim)
  have dep:(schedule ((s).high+(s).low)).length≤3*(L*L):=by rw [room];nlinarith only [sched,square]
  have pro: (t).jobs*prior.venue.cap≤L*L:=Nat.mul_le_mul sites cap
  change 100000*(1+2^prior.venue.k+(schedule ((s).high+(s).low)).length)+
    1000*(1+(t).jobs)*(100+(7+(2*prior.venue.cap)*13))≤_
  have mul : scale J (2*rate)=L*L:=by change scale J (2*rate)=scale J rate*scale J rate;rw [scale_mul,two_mul]
  rw [mul]
  nlinarith only [two,ll,blocks,sites,cap,dep,pro]

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

import OAI.Hierarchy.DescentRegisteredWindowRooms
import OAI.Hierarchy.DescentDatePortInitialHeader

namespace OAI
/-! # The selected initial register on the physical ballot header -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedSeedStartup
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n degree cp nP : ℕ}
  (b : Menu n degree) (X : Catalyst.Approximation F cp nP)
  (R k quota base field wire hist H groups floor w : ℕ)
local notation "chosen" => selectedLayout G S b.payload k b.tail b.gain b.p b.drift b.degreeLimit b.f quota base field wire hist
local notation "grain" => S.grainAt G.b b.p 0
local notation "register" => DatePorts.initial G b.op X R chosen k H groups b.payload grain

theorem initial_register_room (epochs : 0<S.height) (branch : G.b≤2^S.capGain)
    (radix : S.radix=2^k) (firstSites : ∃d,S.initialSites=2^d)
    (scheduled : ∃t reset J M,S=stageNumbers G t J b.f b.gain reset M b.tail)
    (sites : S.hostSize 0≤H) (maxSites : H≤DescentCompiler.TerminalScale.hostRows (S.hostSize 0))
    (waves : groups=S.groupCount 0)
    (after_ : DescentDatedSeedStartup.endAddress X chosen H groups k≤floor) (space : floor<2^w) :
    Rooms G S b k w 0 ⟨register,floor⟩ :=by
  subst groups
  obtain ⟨d,paidSites⟩:=firstSites
  have nonempty : 0<H:=by
    have pos:S.hostSize 0>0:=by simp [AtomSchedule.hostSize,paidSites]
    exact pos.trans_le sites
  exact ⟨DatePorts.initial_widths (p:=b.p) G S b.op X R b.payload k b.tail b.gain b.drift b.degreeLimit b.f quota
      base field wire hist H (S.groupCount 0),
   DatePorts.initial_wire_room G b.op X R chosen k H (S.groupCount 0) b.payload grain floor w after_ space,
   DatePorts.initial_header_room G b.op X R chosen k H (S.groupCount 0) b.payload grain after_ space,
   DatePorts.seed_argument_slots (p:=b.p) G S b.op X R b.payload k b.tail b.gain b.drift b.degreeLimit b.f quota
      base field wire hist H (S.groupCount 0) epochs branch,
   DatePorts.initial_paid_room G b.op X R chosen k H (S.groupCount 0) b.payload grain floor w after_ space,
   DatePorts.initial_port_room G b.op X R chosen k H (S.groupCount 0) b.payload grain floor w after_ space,
   DatePorts.initial_actor_room G b.op X R chosen k H (S.groupCount 0) b.payload grain floor w after_ space,
   DatePorts.seed_population (p:=b.p) G S b.op X R b.payload k b.tail b.gain b.drift b.degreeLimit b.f quota
      base field wire hist H nonempty sites maxSites,radix,⟨d,paidSites⟩,scheduled⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI

import OAI.Hierarchy.DescentRegisteredResetCharges
import OAI.Hierarchy.DescentScheduledVenuePrice

namespace OAI
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset DescentPackedWalsh
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)

theorem registered_venue_tariff (t f g reset D receiver ratio saving : ℕ) :
    ∃ nextRate lead exponent : ℕ,∀(op : RotorSpec) (drift τ B : ℕ), nextRate+2 ≤ B →
      G.b ≤ 2^(capRate G t g) → 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B →
      ∀ᶠ h:ℕ in atTop,∀ copies i p w degree s Z : ℕ,
        let J:=Nat.log 2 h/(2*B)
        let tb:=tail τ J
        let S:=stageNumbers G t J f g reset copies tb
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        ∀(ordinary : ℕ→Dated.Ordinary) (prev : DatePorts) (floor : ℕ)
          (space : ScheduledCodeRoom G S board k tb i p f g drift degree h ordinary op s Z
            prev.operandLanes prev.roleLanes prev.venue prev.io floor w prev.archive),
        let a:=scheduled G S board k tb i p f g drift degree h ordinary op s Z prev.operandLanes prev.roleLanes
          prev.venue prev.io.wire prev.io.roster floor
        i < S.length → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
        (∀j<S.length,j%(S.rounds+1)≠S.rounds→(ordinary j).payload=h ∧
          (ordinary j).unit=(DonorDate.atDate G S g k j p).amount) →
        prev.venue.hosts=S.hostSize i → prev.venue.k=k → prev.venue.degree=D →
        8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
        8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ scale J receiver →
        (DatePorts.resetCharges G S board k tb i p f g drift degree h ordinary op s Z prev floor w space).venue ≤
          S.hostSize i*h*(lead*scale J exponent)+S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)+
            copies/(2^J)^saving :=by
  obtain ⟨next,lead,ex,price⟩:=scheduled_venue_date_tariff G board t f g reset D receiver ratio saving
  refine ⟨next,lead,ex,?_⟩
  intro op drift τ B acquired branch rate
  filter_upwards [price op drift τ B acquired branch rate] with h date
  intro copies i p w degree s Z J tb S k ordinary prev floor space a live small many cpu budget hosts blocks
    degreeAt bits rooms width
  exact date copies i p w degree s Z prev.operandLanes prev.roleLanes ordinary prev.venue prev.io floor
    live small many cpu budget hosts blocks degreeAt bits rooms width

end
end Hierarchy.DescentSixParty.NativePitch

end OAI

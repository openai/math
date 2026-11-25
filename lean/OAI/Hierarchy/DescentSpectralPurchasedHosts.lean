import OAI.Hierarchy.DescentDyadicHostAt
import OAI.Hierarchy.DescentFixedRotorRates
import OAI.Hierarchy.DescentOriginalMachineRatio

namespace OAI
/-! # Pricing the dyadic hosts on the fixed spectral rotor and the purchased native word -/
namespace Hierarchy.DescentSixParty.EpochRotor
open DescentCompiler DescentCompiler.TerminalScale Filter
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} (c : EpochRotor G)

/-- Construct the final host from one purchased original word at the selected height.
All calendar, pitch, receiver, lookup and census witnesses in the premise describe the actual
fixed board. The word ratio is fixed before the terminal tail and bus divisor. -/
def ProducesHosts (drift limit : ℕ) :=
  ∀head dates billed last : ℕ, ∃wordFloor : ℕ, ∀W≥wordFloor, ∃driftR slots τ₀ : ℕ, ∀τ≥τ₀, ∃β₀ : ℕ, ∀β≥β₀,
    ∃cost : ℕ, ∀ᶠ h : ℕ in atTop,
      SeedNamed.OriginalWord G c.board c.spec c.rounds c.f c.g c.reset (cutRate c.rounds c.f c.g) drift limit
        c.branch head dates billed last W τ β h driftR slots →
      DyadicHostAt G c.rounds c.f c.g c.reset τ β cost h

/-- The machine and socket purchases may have different lower thresholds. One
tail and one bus divisor meet all of them, and one height supplies both original witnesses. -/
theorem descent_of_purchased_hosts (drift limit saving : ℕ) (produce : c.ProducesHosts drift limit) :
    CollapseOracle.Descent F :=by
  obtain ⟨minWord,head,dates,billed,last,buy⟩:=SeedNamed.original_machine_above_ratio G c.board c.spec c.rounds
    c.f c.g c.reset (cutRate c.rounds c.f c.g) drift limit c.branch saving
  obtain ⟨hostWord,above⟩:=produce head dates billed last
  let W:=max minWord hostWord
  obtain ⟨driftR,slots,hostTail,hosts⟩:=above W (le_max_right ..)
  obtain ⟨machineTail,machine⟩:=buy W (le_max_left ..) driftR slots
  let τ:=max hostTail machineTail
  obtain ⟨hostBus,produceAt⟩:=hosts τ (le_max_left ..)
  obtain ⟨machineBus,buyAt⟩:=machine τ (le_max_right ..)
  let κ:=1+(hostRate c.rounds c.reset+capRate G c.rounds c.g)*(c.rounds+1)+8+cutRate c.rounds c.f c.g
  let socket:=2*(localSocketRate G c.rounds c.g+(τ+κ+4))+Nat.clog 2 G.b*(c.rounds+1)
  let β:=max (max hostBus machineBus) (socket+1)
  have hhost : hostBus≤β := (le_max_left ..).trans (le_max_left ..)
  have hmachine : machineBus≤β := (le_max_right ..).trans (le_max_left ..)
  have hsocket : socket+1≤β := le_max_right ..
  obtain ⟨cost,build⟩:=produceAt β hhost
  apply descent_of_priced_dyadic_hosts G c.rounds c.f c.g c.reset τ β cost (by omega)
    ((Nat.le_succ socket).trans hsocket)
  filter_upwards [buyAt β hmachine,build] with h granted compiled
  exact compiled granted

end
end Hierarchy.DescentSixParty.EpochRotor

namespace Hierarchy.DescentSixParty
noncomputable section
theorem descent_of_spectral_hosts {F : Type} [Field F] (family : NonlinearExpanders.SpectralFamily F)
    (issued : ∀(G : PoweredGadget F) (c : EpochRotor G), ∃drift limit : ℕ, c.ProducesHosts drift limit) :
    CollapseOracle.Descent F :=by
  obtain ⟨G,⟨c⟩⟩:=powered_rotor_of_family F family
  obtain ⟨drift,limit,hosts⟩:=issued G c
  exact c.descent_of_purchased_hosts drift limit 1 hosts

end
end Hierarchy.DescentSixParty

end OAI

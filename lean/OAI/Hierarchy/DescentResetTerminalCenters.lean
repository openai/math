import OAI.Hierarchy.DescentTerminalDatedScanBefore
import OAI.Hierarchy.DescentResetVenueSourceLower

namespace OAI
/-! Lower addresses of the last reset's counted, compact and normalized input banks. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup ProtocolRAM
noncomputable section

namespace ResetOutput

theorem terminal_centers_above (v : ResetOutput) (step : ℕ) :
    step ≤ v.fundedEnd step ∧
    step ≤ (v.actor.directory (v.middle.stop step)).count.base ∧
    ∀ x, step ≤ (v.terminalActor step x).base := by
  have funded : step ≤ v.fundedEnd step :=
    (show step ≤ v.finalEnd step by rw [v.finalTranslated]; omega).trans
      (v.complete_after step).1
  have mid : step ≤ v.middle.stop step := by rw [v.middle.translated]; omega
  have acquired (base : ℕ) : base ≤ v.actor.endAddress base := by
    obtain ⟨repeatAt,gateAt,outAt⟩ := v.actor.gate_order base
    have beforeRepeat : (v.actor.gate base).scalar ≤ (v.actor.gate base).repeatBase :=
      (Nat.le_add_right ..).trans repeatAt.le
    have beforeGate : (v.actor.gate base).repeatBase ≤ (v.actor.gate base).gateBase := by
      rw [←gateAt]
      unfold DescentSharedLeafLookup.Public.stop
      exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
    have beforeOutput : (v.actor.gate base).gateBase ≤ (v.actor.gate base).output :=
      (Nat.le_add_right ..).trans outAt.le
    have scalarLower : base ≤ (v.actor.gate base).scalar := by
      dsimp [ActorSetup.gate, ActorSetup.next, ActorSetup.heights, ActorSetup.levels,
        ActorSetup.starts, ActorSetup.counts, ActorSetup.depths, ActorSetup.bank]
      omega
    exact scalarLower.trans (beforeRepeat.trans (beforeGate.trans
      (beforeOutput.trans (Nat.le_add_right ..))))
  refine ⟨funded, (mid.trans (acquired _)).trans ?_, ?_⟩
  · change v.actor.endAddress (v.middle.stop step) ≤
      (v.actor.endAddress (v.middle.stop step) + 2 * (v.actor.directory (v.middle.stop step)).pitch) +
        (v.actor.directory (v.middle.stop step)).sites
    omega
  · intro x
    let base := v.venue.venueStart (v.fundedEnd step)
    have venue := v.venue.after (v.fundedEnd step)
    obtain ⟨signed, paid, _, _⟩ := v.venue.next.order base
    have lower : step ≤ v.venue.next.secondEnd base :=
      (((funded.trans venue.1).trans venue.2.1).trans signed).trans paid
    apply lower.trans
    change v.venue.next.secondEnd base ≤
      (DescentVenueSlabs.page v.venue.next.aliveShape (v.venue.next.secondEnd base) x).base
    simp only [DescentVenueSlabs.page, Overlap.outputBank, Overlap.dest, Overlap.dictBase,
      DescentVenueSlabs.work]
    omega

theorem terminal_venue_centers (v : ResetOutput) (step : ℕ) (prior : ResetVenue.Earlier) :
    let base := v.fundedEnd step
    let input := v.venue.sources prior base
    step ≤ input.roster.base ∧ step ≤ input.hub.base ∧ step ≤ v.venue.venueStart base := by
  have lower := (v.terminal_centers_above step).1
  obtain ⟨roster, hub, venue⟩ := v.venue.sources_lower prior (v.fundedEnd step)
  exact ⟨lower.trans roster, lower.trans hub, lower.trans venue⟩

end ResetOutput

theorem PhysicalReset.terminal_centers_above (a : PhysicalReset) (floor : ℕ) :
    let step := a.rebased (a.stageStart floor)
    floor ≤ step ∧ floor ≤ a.successor.fundedEnd step ∧
      floor ≤ (a.successor.actor.directory (a.successor.middle.stop step)).count.base ∧
      ∀ x, floor ≤ (a.successor.terminalActor step x).base := by
  intro step
  have route := a.occupied (a.stageStart floor)
  have early : floor ≤ step :=
    ((a.ingress.after floor).trans route.1).trans route.2.1
  obtain ⟨funded, count, actor⟩ := a.successor.terminal_centers_above step
  exact ⟨early, early.trans funded, early.trans count, fun x => early.trans (actor x)⟩

end
end Hierarchy.DescentDatedAddressBook

end OAI

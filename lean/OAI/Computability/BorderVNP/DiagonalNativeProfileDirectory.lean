import OAI.Computability.BorderVNP.DiagonalNativeCanonicalBoot
import OAI.Computability.BorderVNP.DiagonalNativePublishedWindow

/-! # The true demand directory starts on the decoded enriched profile's output -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open PackedHistoryCircuit Packing
open private before_iff from OAI.Computability.BorderVNP.DiagonalNativePublishedWindow

/-- The physical original-site and demand-directory passes in a complete native
preparation begin in the exact state of the chosen adaptive history. This identifies
the live profile words and charges the original startup, pins and geometry once. -/
theorem beforeRoute_after_profile {w k : ℕ} (f : BroadcastFrame) {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s : Bank w} {initial : Memory w} {es z saved}
    (boot : Runs pub mac JointHeader.bootHeader s initial es z saved) (stable : f.Stable (readings z))
    (positive : (saved f.dst).val ≠ 0)
    (pins : (Fin k → Bool) ≃ Pins.Return pub mac (Function.update z 10 (saved f.dst)) saved)
    (streams : ∀ b, (pins b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b)
    (profile : (Fin k → Bool) ≃ Returns (withStartup pinGeometry) pub mac s initial)
    (guesses : ∀ b, (profile b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b)
    (b : Fin k → Bool) (dim bits : ℕ) (p : Returns (beforeRoute epochPlacement (scheduleGroups dim bits))
      pub mac (pins b).val.2.1 (pins b).val.2.2) :
    ∃ directory : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac
        (profile b).val.2.1 (profile b).val.2.2,
      ∃ groups : Returns (scheduleGroups dim bits) pub mac directory.val.2.1 directory.val.2.2,
        p.val.2=groups.val.2 ∧ traceCost es+2+traceCost (pins b).val.1+traceCost p.val.1 =
          traceCost (profile b).val.1+traceCost directory.val.1+traceCost groups.val.1 := by
  obtain ⟨v,mv,gs,tail,events,g,after⟩ := Runs.seq_iff.mp ((before_iff dim bits).mp p.property)
  obtain ⟨u,mu,ds,ss,rfl,place,schedule⟩ := Runs.seq_iff.mp after
  have same := profile_at_pin_return f boot stable positive pins streams profile guesses b ⟨(gs,v,mv),g⟩
  obtain ⟨state,_,ticks⟩ := same
  rw [state]
  refine ⟨⟨(ds,u,mu),place⟩,⟨(ss,p.val.2),schedule⟩,rfl,?_⟩
  rw [events,ticks]
  simp only [traceCost,RAMBuckets.cost_append]
  change _ + (traceCost gs + (traceCost ds + traceCost ss)) = _ + traceCost gs + traceCost ds + traceCost ss
  omega

/-- Use the directory actually published on an authenticated profile return to charge
all preceding instructions and the true eleven-pass group scheduler. The descriptor and
declaration clocks refer to that publication's memory. -/
theorem profile_schedule_charge {w k : ℕ} (f : BroadcastFrame) {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s : Bank w} {initial : Memory w} {es z saved}
    (boot : Runs pub mac JointHeader.bootHeader s initial es z saved) (stable : f.Stable (readings z))
    (positive : (saved f.dst).val ≠ 0)
    (pins : (Fin k → Bool) ≃ Pins.Return pub mac (Function.update z 10 (saved f.dst)) saved)
    (streams : ∀ b, (pins b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b)
    (profile : (Fin k → Bool) ≃ Returns (withStartup pinGeometry) pub mac s initial)
    (guesses : ∀ b, (profile b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b)
    (b : Fin k → Bool) (dim bits zLabels time entries teams sites : ℕ) (p : ScheduleClock.Placements)
    (paid : traceCost (profile b).val.1 ≤ time)
    (directory : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac (profile b).val.2.1 (profile b).val.2.2)
    (scan : traceCost directory.val.1 ≤ deliveryScanTicks entries teams sites)
    (ready : ScheduleClock.AtEntries pub mac (ScheduleClock.passes pub mac zLabels dim bits directory.val.2.2 p)
      directory.val.2.1 directory.val.2.2)
    (r : Returns (beforeRoute epochPlacement (scheduleGroups dim bits)) pub mac (pins b).val.2.1 (pins b).val.2.2) :
    let mem := readings directory.val.2.2
    let labels := Cube.LabelIndex.layout (pub 0).val mem
    traceCost es+2+traceCost (pins b).val.1+traceCost r.val.1 ≤ time+
      ScheduleClock.beforeDirectory teams sites entries+ScheduleClock.descriptorTicks labels mem zLabels p.header.a p.groups p.teams+
      ScheduleClock.declarationTicks (p.header.decoder p.broadcast) dim bits := by
  intro mem labels
  obtain ⟨actual,groups,_,joined⟩ := beforeRoute_after_profile f boot stable positive pins streams profile guesses b dim bits r
  have same : actual = directory := by
    obtain ⟨events,bank,memory⟩ := actual.property.unique_of_deterministic (by decide) directory.property
    exact Subtype.ext (Prod.ext events (Prod.ext bank memory))
  subst actual
  have cost := ScheduleClock.scheduleGroups_traceCost pub mac zLabels dim bits p ready groups.property
  change traceCost groups.val.1 ≤ ScheduleClock.descriptorTicks labels mem zLabels p.header.a p.groups p.teams +
    ScheduleClock.declarationTicks (p.header.decoder p.broadcast) dim bits at cost
  have scanned : traceCost directory.val.1 ≤ ScheduleClock.beforeDirectory teams sites entries := by
    simpa only [deliveryScanTicks,ScheduleClock.beforeDirectory,Nat.add_assoc] using scan
  omega

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.DiagonalParsedProfileReturn
import OAI.Computability.BorderVNP.RoutingISASignedPrepRange

/-! # The geometry and directory prefix tested by signed declaration guards -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP.BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator RoutingISA.CompactMachine
open PackedHistoryCircuit Packing CellMacro.Generator BorderVNP.Cube JointHeader
open private before_iff from OAI.Computability.BorderVNP.DiagonalNativePublishedWindow

variable {w k : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s : Bank w} {initial : Memory w} {trace out saved} (f : BroadcastFrame)
variable (boot : Runs pub mac bootHeader s initial trace out saved) (stable : f.Stable (readings out))
    (positive : (saved f.dst).val ≠ 0)
    (pins : (Fin k → Bool) ≃ Pins.Return pub mac (Function.update out 10 (saved f.dst)) saved)
    (pinChoices : ∀ v, (pins v).val.1.flatMap TeamRAM.Event.choices = List.ofFn v)
    (profile : (Fin k → Bool) ≃ Returns (withStartup pinGeometry) pub mac s initial)
    (readChoices : ∀ v, (profile v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v)

include boot stable positive pinChoices readChoices in
/-- Publish the authenticated geometry at the actual start of a recorded
preparation. The resulting prefix has empty choice stream, even if the
unchecked declaration or later report will be rejected. -/
theorem pinnedPublicationRun {dim bits : ℕ} (v : Fin k → Bool)
    (p : Returns (beforeRoute epochPlacement (scheduleGroups dim bits)) pub mac (pins v).val.2.1 (pins v).val.2.2)
    {publication : List (TeamRAM.Event w)} {dest : Bank w} {memory : Memory w}
    (publish : Runs pub mac (.seq PrivatePlacement.program Directory.ISA.program)
      (profile v).val.2.1 (profile v).val.2.2 publication dest memory) :
    ∃ es, Runs pub mac (.seq epochPlacement Directory.ISA.program)
      (pins v).val.2.1 (pins v).val.2.2 es dest memory ∧ es.flatMap TeamRAM.Event.choices=[] := by
  obtain ⟨z,m,gs,_,_,geometry,_⟩ := Runs.seq_iff.mp ((before_iff dim bits).mp p.property)
  obtain ⟨state,none,_⟩ := profile_at_pin_return f boot stable positive pins pinChoices profile readChoices v
    ⟨(gs,z,m),geometry⟩
  obtain ⟨z',m',es,ds,eq,slot,directory⟩ := Runs.seq_iff.mp publish
  change (profile v).val.2 = (z,m) at state
  rw [state] at slot
  refine ⟨(gs++es)++ds,(geometry.seq slot).seq directory,?_⟩
  have silent : publication.flatMap TeamRAM.Event.choices = [] :=
    List.flatMap_eq_nil_iff.mpr (fun a ha => (publish.unsigned_events (by decide) a ha).1)
  simpa only [eq, List.flatMap_append, none, List.nil_append] using silent

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI

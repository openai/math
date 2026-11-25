import OAI.Computability.BorderVNP.DiagonalNativeCanonicalBoot
import OAI.Computability.BorderVNP.PackedRoutingPublishedRun

/-! # Publishing the reached frozen profile after its own physical pin return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP.BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator RoutingISA.CompactMachine
open PackedHistoryCircuit Packing

variable {w k : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s : Bank w} {initial : Memory w} {trace out saved} (f : BroadcastFrame)
    (boot : Runs pub mac JointHeader.bootHeader s initial trace out saved) (stable : f.Stable (readings out))
    (positive : (saved f.dst).val ≠ 0)
    (pins : (Fin k → Bool) ≃ Pins.Return pub mac (Function.update out 10 (saved f.dst)) saved)
    (pinChoices : ∀ v, (pins v).val.1.flatMap TeamRAM.Event.choices = List.ofFn v)
    (profile : (Fin k → Bool) ≃ Returns (withStartup pinGeometry) pub mac s initial)
    (readChoices : ∀ v, (profile v).val.1.flatMap TeamRAM.Event.choices = List.ofFn v)

include boot stable positive pinChoices readChoices in
/-- Decompose the complete profile run on its selected Boolean pin. The
geometry finishes at exactly the returned RAM and registers, with its
entire clock accounted for before any group or private call. -/
theorem chosenGeometryAfterPin (v : Fin k → Bool) :
    ∃ geo : Returns GeometryAdvice.reconstruct pub mac (pins v).val.2.1 (pins v).val.2.2,
      geo.val.2 = (profile v).val.2 ∧ geo.val.1.flatMap TeamRAM.Event.choices=[] ∧
        traceCost (profile v).val.1 = traceCost trace+2+traceCost (pins v).val.1+traceCost geo.val.1 := by
  obtain ⟨z,m,pre,head,rfl,start,copy⟩ := Runs.seq_iff.mp boot
  obtain ⟨rest,shape,tail⟩ := (evaluation_startup_iff f pinGeometry start copy stable positive).mp (profile v).property
  obtain ⟨r,mem,ps,gs,split,prepare,read⟩ := Runs.seq_iff.mp tail
  let chosen : Pins.Return pub mac (Function.update out 10 (saved f.dst)) saved := ⟨(ps,r,mem),prepare⟩
  obtain ⟨a,ha⟩ := pins.surjective chosen
  have events : (pins a).val.1 = ps := congrArg (fun t => t.val.1) ha
  have exactPin : ps.flatMap TeamRAM.Event.choices = List.ofFn a := events ▸ pinChoices a
  have none : (dispatchPrefix f saved pre head).flatMap TeamRAM.Event.choices = [] :=
    List.flatMap_eq_nil_iff.mpr fun e he => List.length_eq_zero_iff.mp
      (Nat.eq_zero_of_le_zero ((dispatchPrefix_effects f start copy).1.choices e he))
  have stream := readChoices v
  rw [shape,split,List.flatMap_append,none,List.nil_append,List.flatMap_append,exactPin] at stream
  have len := congrArg List.length stream
  simp only [List.length_append,List.length_ofFn] at len
  have silent : gs.flatMap TeamRAM.Event.choices = [] := List.length_eq_zero_iff.mp (by omega)
  rw [silent,List.append_nil] at stream
  obtain rfl := List.ofFn_injective stream
  have pair : (pins a).val.2 = (r,mem) := congrArg (fun t => t.val.2) ha
  have actual : Runs pub mac GeometryAdvice.reconstruct (pins a).val.2.1 (pins a).val.2.2 gs
      (profile a).val.2.1 (profile a).val.2.2 := by
    rw [pair]
    exact read
  let geo : Returns GeometryAdvice.reconstruct pub mac (pins a).val.2.1 (pins a).val.2.2 :=
    ⟨(gs,(profile a).val.2),actual⟩
  exact ⟨geo,rfl,silent,(profile_at_pin_return f (start.seq copy) stable positive pins pinChoices profile readChoices a geo).2.2⟩

include boot stable positive pinChoices readChoices in
/-- A fitted placement and publication on the profile's output give the two
actual consecutive stage returns on that pin, with the same intermediate and
final RAM, even before the group scheduler has run. -/
theorem chosenPin_publication (v : Fin k → Bool) {es fs mid placed after published}
    (place : Runs pub mac PrivatePlacement.program (profile v).val.2.1 (profile v).val.2.2 es mid placed)
    (publish : Runs pub mac Directory.ISA.program mid placed fs after published) :
    ∃ epoch : Returns epochPlacement pub mac (pins v).val.2.1 (pins v).val.2.2,
    ∃ dir : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2,
      epoch.val.2=(mid,placed) ∧ dir.val=(fs,after,published) ∧
      epoch.val.1.flatMap TeamRAM.Event.choices=[] ∧ dir.val.1.flatMap TeamRAM.Event.choices=[] ∧
      traceCost trace+2+traceCost (pins v).val.1+traceCost epoch.val.1+traceCost dir.val.1 =
        traceCost (profile v).val.1+traceCost es+traceCost fs := by
  obtain ⟨geo,endState,silent,cost⟩ := chosenGeometryAfterPin f boot stable positive pins pinChoices profile readChoices v
  have first := geo.property
  change Runs pub mac GeometryAdvice.reconstruct _ _ geo.val.1 (geo.val.2).1 (geo.val.2).2 at first
  rw [endState] at first
  let epoch : Returns epochPlacement pub mac (pins v).val.2.1 (pins v).val.2.2 :=
    ⟨(geo.val.1++es,mid,placed),first.seq place⟩
  have ep : es.flatMap TeamRAM.Event.choices=[] := List.flatMap_eq_nil_iff.mpr fun a ha => (place.unsigned_events (by decide) a ha).1
  have de : fs.flatMap TeamRAM.Event.choices=[] := List.flatMap_eq_nil_iff.mpr fun a ha => (publish.unsigned_events (by decide) a ha).1
  refine ⟨epoch,⟨(fs,after,published),publish⟩,rfl,rfl,?_,de,?_⟩
  · change (geo.val.1++es).flatMap TeamRAM.Event.choices=[]
    simp only [List.flatMap_append,silent,ep,List.nil_append]
  · change _ + traceCost (geo.val.1++es) + traceCost fs = _
    rw [Transmission.cost_append,cost]
    omega

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI

import OAI.Computability.VPVNP.CompressorScheduledExecution

/-! # The two concrete source constructors of the descriptor calendar

The semantic origin fixes the input graph and the precise shrinking index
or refresh pass. Equality with the physical window index identifies the
native worker in the finite script. The remaining bounds are available for
the input graph and every immediate selected successor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace
open Compression PassTimeline
attribute [local irreducible] BlockProgram.script

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
variable {w cap small rate total T P M : ℕ} {pub : Fin 11 → BurstRAM.Word w} {pitch : BurstRAM.Word w}
variable {resident : Resident B f hf w}

/-- A native execution for one pass origin at its specified block and substep, from every ready memory. -/
abbrev EmitAt (resident : Resident B f hf w) (pub : Fin 11 → BurstRAM.Word w) (pitch : BurstRAM.Word w)
    (total cap small rate T P M : ℕ) {a g b n : ℕ} {X : State a g} {p : StatePass R X b n}
    (o : PassOrigin B f hf p) (loc : Located S.steps) :=
  ∀ (encode : p.step.Choice → List Bool) (past : List (SelectedLevel B f hf)) (m : BurstRAM.Memory w),
    loc.block < T → past.length = loc.depth → X.positions ≤ P → X.maxWireWidth ≤ M →
    (∀ i, (p.next i).positions ≤ P ∧ (p.next i).maxWireWidth ≤ M) →
    Boundary resident pub pitch total (loc.first B) past X m →
    Nonempty (PassRun resident pub pitch total cap small rate loc o encode past m)

/-- These two local constructors suffice for the actual iterated program.
Only valid shrinking indices occur, and the identity cast of the lane count
makes the shrinking input exactly the packing state expected by its worker. -/
theorem locatedRuns_of_passes
    (shrink : ∀ (i : Fin S.steps) (g t : ℕ) (X : State (S.degreeExponent i.castSucc)
      (packingLaneBits (S.degreeExponent i.castSucc) g)),
      EmitAt resident pub pitch total cap small rate T P M (PassOrigin.shrink i rfl X) ⟨t,.shrink i⟩)
    (refresh : ∀ (g t : ℕ) (X : State S.portExponent (S.portExponent+g)),
      EmitAt resident pub pitch total cap small rate T P M (PassOrigin.refresh X) ⟨t,.refresh⟩) :
    LocatedRuns resident pub pitch total cap small rate T P M := by
  intro a g b n X p o encode loc past m hphase
  obtain ⟨t,s⟩ := loc
  cases o with
  | shrink i h Y =>
    subst h
    cases s with
    | shrink j =>
      have eq : i = j := Fin.ext (ExecutionCalendar.Phase.shrink.inj hphase)
      subst j
      exact shrink i _ t _ encode past m
    | refresh => contradiction
  | refresh Y =>
    cases s with
    | shrink i => contradiction
    | refresh => exact refresh _ t Y encode past m

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI

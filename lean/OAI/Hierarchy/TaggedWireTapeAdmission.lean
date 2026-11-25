import OAI.Hierarchy.TaggedWirePathEncoding
import OAI.Hierarchy.TaggedWireCalendarShelf

namespace OAI
/-! # The native calendar tape and its unique accepted chronological path -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical

variable {X : Type} {W q d : ℕ} (slot : Event→Slot X)

def actual (C : Chart W q d) (read : ∀e,Memory W→Bits (slot e).bits) :
    (es : List Event)→Memory W→Bits (bits slot es)
  | [],_=>Fin.elim0
  | e::es,m=>Fin.addCases (read e m) (actual C read es (after C e m))

/-- The one complete checked tape has exactly the sum of the native event
widths. There are no unobserved high rows to multiply a branch's weight. -/
theorem admissible_iff (C : Chart W q d) (read : ∀e,Memory W→Bits (slot e).bits)
    (state : List Event→X→Memory W→Prop)
    (accept : ∀e es x m,state (e::es) x m →
      (accepted C e m ↔ ∃c,(slot e).word x c=read e m))
    (step : ∀e es x m,state (e::es) x m → ∀c,(slot e).word x c=read e m →
      state es ((slot e).next x c) (after C e m))
    (es : List Event) (x : X) (m : Memory W) (start : state es x m) :
    admissible C es m ↔ ∃! j : Path slot es x, encode slot es x j=actual slot C read es m := by
  have image : admissible C es m ↔ ∃ j : Path slot es x,encode slot es x j=actual slot C read es m := by
    induction es generalizing x m with
    | nil =>
      constructor
      · intro _
        exact ⟨(),funext fun i=>Fin.elim0 i⟩
      · intro _
        trivial
    | cons e es ih =>
      constructor
      · rintro ⟨head,tail⟩
        obtain ⟨a,wi⟩ := (accept e es x m start).mp head
        obtain ⟨p,rest⟩ := (ih _ _ (step e es x m start a wi)).mp tail
        refine ⟨⟨a,p⟩,?_⟩
        change (Fin.addCases ((slot e).word x a) (encode slot es _ p) : Bits ((slot e).bits+bits slot es)) =
          Fin.addCases (read e m) (actual slot C read es (after C e m))
        rw [wi,rest]
      · rintro ⟨⟨a,p⟩,he⟩
        change (Fin.addCases ((slot e).word x a) (encode slot es _ p) : Bits ((slot e).bits+bits slot es)) =
          Fin.addCases (read e m) (actual slot C read es (after C e m)) at he
        have first : (slot e).word x a=read e m := funext fun i=>by
          simpa only [Fin.addCases_left]
            using congrFun he (Fin.castAdd (bits slot es) i)
        refine ⟨(accept e es x m start).mpr ⟨a,first⟩,(ih _ _ (step e es x m start a first)).mpr ⟨p,?_⟩⟩
        funext i
        simpa only [Fin.addCases_right]
          using congrFun he (Fin.natAdd (slot e).bits i)
  refine image.trans ⟨?_,fun h=>h.exists⟩
  rintro ⟨j,eqn⟩
  exact ⟨j,eqn,fun a h=>(encode slot es x).injective (h.trans eqn.symm)⟩

end Hierarchy.WireTelescope.CalendarTape

end
end OAI

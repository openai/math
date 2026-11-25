import OAI.Hierarchy.TaggedWireCalendarShelf
import OAI.Hierarchy.TaggedWireTelescope

namespace OAI
/-! # The native admission flag recognizes the telescope's chronological private words -/

noncomputable section
namespace Hierarchy.WireTelescope
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM ProtocolRAM.Calendar
open ThreeFlat.RAM
open scoped Classical

variable {W q d B : ℕ} {X : Type*}
variable (choices : X→Type) (next : ∀x,choices x→X)
variable (encode : ∀x,choices x ↪ Tagged.Bits B)

/-- Each field is observed in the actual memory at its chronological event.
For an attempt this is the guarded histogram tape established by
`HistogramShelf.calendar_field`. -/
def calendarFields (C : Chart W q d) (word : Event→Memory W→Tagged.Bits B) :
    (es : List Event) → Memory W → Fin es.length → Tagged.Bits B
  | [],_=>Fin.elim0
  | e::es,m=>Fin.cases (word e m) (calendarFields C word es (after C e m))

/-- The pointwise tests come from admission at a purchased packet's true
snapshot. The second premise transfers the physical stock representation
after its accepted local choice (feed events use their forced empty word).
Together they identify the image of all admissible complete executions. -/
theorem admissible_iff_history (C : Chart W q d) (word : Event→Memory W→Tagged.Bits B)
    (related : List Event→X→Memory W→Prop)
    (accept : ∀ e es x m,related (e::es) x m →
      (accepted C e m ↔ ∃ a,encode x a=word e m))
    (advance : ∀ e es x m,related (e::es) x m → ∀ a,encode x a=word e m →
      related es (next x a) (after C e m))
    (es : List Event) (x : X) (m : Memory W) (start : related es x m) :
    admissible C es m ↔ ∃! j : History choices next es.length x,
      fields choices next encode es.length x j=calendarFields C word es m := by
  have image : admissible C es m ↔ ∃ j : History choices next es.length x,
      fields choices next encode es.length x j=calendarFields C word es m := by
    induction es generalizing x m with
    | nil =>
      constructor
      · intro _
        exact ⟨(),funext fun i=>Fin.elim0 i⟩
      · intro _
        trivial
    | cons e es ih =>
      constructor
      · rintro ⟨hd,tl⟩
        obtain ⟨a,wordEq⟩ := (accept e es x m start).mp hd
        obtain ⟨h,tailEq⟩ := (ih (next x a) (after C e m) (advance e es x m start a wordEq)).mp tl
        refine ⟨⟨a,h⟩,?_⟩
        funext i
        refine Fin.cases ?_ (fun j=>?_) i
        · exact wordEq
        · exact congrFun tailEq j
      · rintro ⟨⟨a,h⟩,eqn⟩
        have wordEq : encode x a=word e m := congrFun eqn 0
        refine ⟨(accept e es x m start).mpr ⟨a,wordEq⟩,
          (ih (next x a) (after C e m) (advance e es x m start a wordEq)).mpr ⟨h,?_⟩⟩
        funext i
        exact congrFun eqn i.succ
  refine image.trans ⟨?_,fun h=>h.exists⟩
  rintro ⟨j,eqn⟩
  exact ⟨j,eqn,fun j' he=>(fields choices next encode es.length x).injective (he.trans eqn.symm)⟩

end Hierarchy.WireTelescope

end
end OAI

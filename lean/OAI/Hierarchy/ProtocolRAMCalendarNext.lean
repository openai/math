import OAI.Hierarchy.ProtocolRAMCalendarPrevious

namespace OAI
/-! # Successive events on the physical outer and reserve calendar -/
namespace Hierarchy.ProtocolRAM.Calendar

def eventInRange (c : Mesh) : Event→Prop
  | .attempt (.outer p a) => p<c.inject+c.cool ∧ a<c.outerFuel
  | .attempt (.inner p a j b) => p<c.inject+c.cool ∧ a<c.outerFuel ∧ j<c.reserveSteps ∧ b<c.innerFuel
  | .feed (.inner p a j) => p<c.inject+c.cool ∧ a<c.outerFuel ∧ j<c.reserveSteps
  | .feed (.outer p) => p<c.inject+c.cool

theorem eventInRange_iff (c : Mesh) (e : Event) : eventInRange c e ↔ e∈events c := by
  cases e with
  | attempt x =>
    cases x <;> simp [eventInRange,events,outerBlock,trialBlock,reserveBlock,List.mem_flatMap,List.mem_map]

  | feed x =>
    cases x <;> simp [eventInRange,events,outerBlock,trialBlock,reserveBlock,List.mem_flatMap,List.mem_map]


/-- The phase feed occupies the first position after all its trials. -/
def nextTrialStart (c : Mesh) (p a : ℕ) : Event :=
  if a<c.outerFuel then .attempt (.outer p a) else .feed (.outer p)

/-- A slice with zero inner fuel consists of its feed. An empty reserve block
passes directly to the next trial or to the phase feed. -/
def nextSliceStart (c : Mesh) (p a j : ℕ) : Event :=
  if j<c.reserveSteps then
    if 0<c.innerFuel then .attempt (.inner p a j 0) else .feed (.inner p a j)
  else nextTrialStart c p (a+1)

def nextEvent (c : Mesh) : Event→Option Event
  | .attempt (.outer p a) => some (nextSliceStart c p a 0)
  | .attempt (.inner p a j b) =>
    if b+1<c.innerFuel then some (.attempt (.inner p a j (b+1))) else some (.feed (.inner p a j))
  | .feed (.inner p a j) => some (nextSliceStart c p a (j+1))
  | .feed (.outer p) =>
    if p+1<c.inject+c.cool then some (nextTrialStart c (p+1) 0) else none

private theorem trial_start (c : Mesh) (p a : ℕ) (phase : p<c.inject+c.cool) (trial : a≤c.outerFuel) :
    eventInRange c (nextTrialStart c p a) ∧ position c (nextTrialStart c p a)=trialBase c p a := by
  by_cases live : a<c.outerFuel
  · simp [nextTrialStart,live,eventInRange,phase,position]
  · have stop : a=c.outerFuel := by omega
    simp [nextTrialStart,eventInRange,phase,stop,position,trialBase]

private theorem slice_start (c : Mesh) (p a j : ℕ) (phase : p<c.inject+c.cool) (trial : a<c.outerFuel)
    (slice : j≤c.reserveSteps) :
    eventInRange c (nextSliceStart c p a j) ∧ position c (nextSliceStart c p a j)=sliceBase c p a j := by
  by_cases live : j<c.reserveSteps
  · by_cases fuel : 0<c.innerFuel
    · simp [nextSliceStart,live,fuel,eventInRange,phase,trial,position]
    · have empty : c.innerFuel=0 := by omega
      simp [nextSliceStart,live,empty,eventInRange,phase,trial,position]
  · have stop : j=c.reserveSteps := by omega
    obtain ⟨ok,idx⟩:=trial_start c p (a+1) phase trial
    rw [nextSliceStart,ite_eq_right live]
    refine ⟨ok,idx.trans ?_⟩
    rw [stop]
    unfold sliceBase trialBase trialSize
    ring

private theorem step_index (c : Mesh) (e : Event) (valid : eventInRange c e) :
    match nextEvent c e with
    | some f => eventInRange c f ∧ position c f=position c e+1
    | none => (events c).length=position c e+1 := by
  cases e with
  | attempt x =>
    cases x with
    | outer p a =>
      obtain ⟨ph,at_⟩:=valid
      obtain ⟨good,idx⟩:=slice_start c p a 0 ph at_ (Nat.zero_le _)
      exact ⟨good,by simpa [position,sliceBase] using idx⟩
    | inner p a j b =>
      obtain ⟨ph,at_,sl,rep⟩:=valid
      by_cases next : b+1<c.innerFuel
      · simp [nextEvent,next,eventInRange,ph,at_,sl,position,Nat.add_assoc]
      · have stop : b+1=c.innerFuel := by omega
        simp only [nextEvent,ite_eq_right next,eventInRange,position]
        exact ⟨⟨ph,at_,sl⟩,by omega⟩
  | feed x =>
    cases x with
    | inner p a j =>
      obtain ⟨ph,at_,sl⟩:=valid
      obtain ⟨good,idx⟩:=slice_start c p a (j+1) ph at_ sl
      refine ⟨good,idx.trans ?_⟩
      unfold position sliceBase sliceSize
      ring
    | outer p =>
      change p<c.inject+c.cool at valid
      by_cases next : p+1<c.inject+c.cool
      · simp only [nextEvent,ite_eq_left next]
        obtain ⟨ok,idx⟩:=trial_start c (p+1) 0 next (Nat.zero_le _)
        refine ⟨ok,idx.trans ?_⟩
        unfold trialBase position phaseSize
        ring
      · have stop : c.inject+c.cool=p+1 := by omega
        simp only [nextEvent,ite_eq_right next]
        rw [event_count,stop]
        unfold position phaseSize trialSize sliceSize
        ring

theorem next_at (c : Mesh) (u : ℕ) (on : u<(events c).length) :
    (events c)[u+1]?=nextEvent c (events c)[u] := by
  let e:=(events c)[u]
  have here : position c e=u := position_at c on
  have active : eventInRange c e := (eventInRange_iff c e).mpr (List.getElem_mem on)
  have step:=step_index c e active
  change (events c)[u+1]?=nextEvent c e
  cases kind : nextEvent c e with
  | none =>
    rw [kind] at step
    change (events c).length=position c e+1 at step
    exact List.getElem?_eq_none (by omega)
  | some f =>
    rw [kind] at step
    obtain ⟨ok,idx⟩:=step
    obtain ⟨v,fit,same⟩:=List.mem_iff_getElem.mp ((eventInRange_iff c f).mp ok)
    have address:=position_at c fit
    rw [same,idx,here] at address
    subst v
    exact List.getElem?_eq_some_iff.mpr ⟨fit,same⟩

end Hierarchy.ProtocolRAM.Calendar

end OAI

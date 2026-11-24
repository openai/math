import OAI.Computability.VPVNP.RAMTapeSortGatherPreserve
import OAI.Computability.VPVNP.EvaluatorRadixDivision

/-! # The physical block moves between sorting layers

Before a cross-site layer, split the outgoing block off the incident stream.
The received block and all later fields stay in order on the incident stack.
After the row loop, release the previous local block and expose the accumulated
next block in increasing row order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortBoundary

open EvaluatorRadixDivision (reverseOnto reverseOnto_runs)

/-- Stacks holding the current and next blocks, sent and received incident data, word width,
slot count and two temporary buffers. -/
inductive Port where
  | current | next | crossSend | crossReceive | width | slots | scratch1 | scratch2
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

private def gatherPorts : SortGather.Port → Port
  | .block => .crossReceive
  | .offset => .scratch1
  | .width => .width
  | .widthBack => .crossSend
  | .saved => .scratch2
  | .recordBack => .current
  | .output => .next

private theorem injective_gatherPorts : Function.Injective gatherPorts := by
  intro i j h
  cases i <;> cases j <;> first | rfl | cases h

private def copySlots := SuccessorFields.prependCopy Port.slots .scratch1 .scratch2

/-- Separate the leading block of the incident stream in forward bit order. -/
def splitCross : FiniteRoutine Port :=
  (copySlots.followedBy (SortGather.skip.onPorts gatherPorts)).followedBy
    (reverseOnto .scratch2 .crossSend)

/-- Tick cost for separating a complete outgoing block of five-word records from the incident
stream and restoring it in forward bit order. -/
def splitCost (slots w : ℕ) := slots*(40*w+17)+4

theorem splitCross_runs (n w : ℕ) (s : Stacks Port) (data tail : List Bool)
    (hlen : data.length = n*(5*w)) (hb : s .crossReceive = data ++ tail)
    (hc : s .crossSend = []) (hw : s .width = List.replicate w true)
    (hn : s .slots = List.replicate n true) (ht : s .scratch1 = []) (hu : s .scratch2 = []) :
    splitCross.Runs (splitCost n w) s
      (Function.update (Function.update s .crossReceive tail) .crossSend data) := by
  let m := Function.update s Port.scratch1 (List.replicate n true)
  have copy := SuccessorFields.prependCopy_runs Port.slots .scratch1 .scratch2
    (by decide) (by decide) (by decide) s hu
  rw [hn, ht, List.append_nil, List.length_replicate] at copy
  let u := Function.update (Function.update s Port.crossReceive tail) .scratch2 data.reverse
  have move := SortGather.skip_runs w n data tail [] (s .current) (s .next) hlen
  simp only [List.append_nil] at move
  have lifted : (SortGather.skip.onPorts gatherPorts).Runs (n*(30*w+12)+1) m u := by
    apply SortGather.skip.runs_onPorts_framed injective_gatherPorts move
    · intro j
      cases j <;> simp [gatherPorts, SortGather.store, m, hb, hw, hu, hc]
    · intro j
      cases j <;> simp [gatherPorts, SortGather.store, u, ht, hw, hc]
    · intro j hj
      have h₁ := Ne.symm (hj .block)
      have h₂ := Ne.symm (hj .saved)
      have h₃ := Ne.symm (hj .offset)
      simp only [gatherPorts] at h₁ h₂ h₃
      simp [u, m, h₁, h₂, h₃]
  let out := Function.update (Function.update s Port.crossReceive tail) .crossSend data
  have rewind := reverseOnto_runs (src := Port.scratch2) (dst := .crossSend) (by decide) u out
    (by simp [out, hu]) (by simp [u, out, hc]) (by
      intro j h₁ h₂
      simp [u, out, h₁, h₂])
  simp only [u, Function.update_self, List.length_reverse, hlen] at rewind
  have h := (FiniteRoutine.Runs.followedBy copy lifted).followedBy rewind
  unfold splitCross copySlots
  convert h using 1
  unfold splitCost
  ring

private def clearCurrent : FiniteRoutine Port := .ofRoutine {
  entry := ()
  code := fun _ => .pop .current fun b => b.map fun _ => () }

private theorem clearCurrent_runs (s : Stacks Port) :
    clearCurrent.Runs ((s .current).length+1) s (Function.update s .current []) := by
  generalize hx : s Port.current = xs
  induction xs generalizing s with
  | nil =>
    have hp := StackStep.pop (s := s) (code := clearCurrent.body.standalone)
      (q := some clearCurrent.body.entry)
      (show clearCurrent.body.standalone (some clearCurrent.body.entry) =
          .pop .current (fun b => b.map fun _ => ()) from rfl)
    rw [hx] at hp
    exact .cons hp (.nil ..)
  | cons b xs ih =>
    have hp := StackStep.pop (s := s) (code := clearCurrent.body.standalone)
      (q := some clearCurrent.body.entry)
      (show clearCurrent.body.standalone (some clearCurrent.body.entry) =
          .pop .current (fun b => b.map fun _ => ()) from rfl)
    rw [hx] at hp
    have hr := ih (Function.update s .current xs) (Function.update_self ..)
    rw [Function.update_idem] at hr
    exact .cons hp hr

/-- Install the completed row outputs as the input of the following layer. -/
def advance : FiniteRoutine Port := clearCurrent.followedBy (reverseOnto .next .current)

theorem advance_runs (s : Stacks Port) :
    advance.Runs ((s .current).length + 2*(s .next).length + 2) s
      (Function.update (Function.update s .next []) .current (s .next).reverse) := by
  let m := Function.update s Port.current []
  let out := Function.update (Function.update s Port.next []) .current (s .next).reverse
  have move := reverseOnto_runs (src := Port.next) (dst := .current) (by decide) m out
    (by simp [out]) (by simp [out, m]) (by intro j h₁ h₂; simp [m, out, h₁, h₂])
  have h := FiniteRoutine.Runs.followedBy (clearCurrent_runs s) move
  change advance.Runs ((s .current).length+1+(2*(s .next).length+1)) s out at h
  exact (show (s .current).length+1+(2*(s .next).length+1) = (s .current).length+2*(s .next).length+2
    by omega) ▸ h

end RAMTape.SortBoundary

end VPVNP
end Computability
end OAI

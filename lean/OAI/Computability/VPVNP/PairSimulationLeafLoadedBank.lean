import OAI.Computability.VPVNP.PairSimulationLeafPortTable
import OAI.Computability.VPVNP.PairSimulationDFSDecode

/-!
# Exact private workspace after initializing a virtual validator

The stack bank determines every word inside its occupied intervals.
Outside them initialization preserves the old word, including stale cells
from earlier leaves in the same private call. This determines the scratch
state passed to the native stack interpreter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafLoadedBank

open BurstRAM PrivateRAM PrimedInputRAM RAMTape StackMachine LeafStartup LeafRegisterBank

variable {K : Type} {w : ℕ} (L : Layout K w) (s : Stacks K)

/-- Addresses actually written for one occupied stack. -/
def occupies (a : Word w) (j : K) := L.base j ≤ a.val ∧ a.val < L.base j + (s j).length

open scoped Classical in
/-- Look up the encoded bit occupying a private stack address, counting from the bottom of the
stack. Return none for an unoccupied address. -/
noncomputable def readCell (a : Word w) : Option (Word w) :=
  if h : ∃ j, occupies L s a j then
    let j := Classical.choose h
    let hj := Classical.choose_spec h
    let i := a.val - L.base j
    have inside : i < (s j).reverse.length := by
      change L.base j ≤ a.val ∧ a.val < L.base j + (s j).length at hj
      simp only [List.length_reverse, i]; omega
    some (encodeBit w (s j).reverse[i])
  else none

/-- Initialize occupied private stack cells with their encoded bits and retain the old memory
at every other address. -/
noncomputable def memory (old : Word w → Word w) (a : Word w) : Word w :=
  (readCell L s a).getD (old a)

theorem readCell_value (mem : Word w → Word w) (contents : L.Contents mem s)
    (fit : ∀ j, (s j).length ≤ L.capacity) (a : Word w) (hwritten : ∃ j, occupies L s a j) :
    readCell L s a = some (mem a) := by
  classical
  let j := Classical.choose hwritten
  have hj : L.base j ≤ a.val ∧ a.val < L.base j+(s j).length := Classical.choose_spec hwritten
  let i := a.val-L.base j
  let ix := (s j).length-1-i
  have hi : i < (s j).length := by dsimp [i]; omega
  have hx : ix < (s j).length := by dsimp [ix]; omega
  let tail := (s j).drop (ix+1)
  have he : s j = (s j).take ix ++ (s j)[ix] :: tail := by
    rw [show (s j)[ix] :: tail = (s j).drop ix from List.getElem_cons_drop hx,List.take_append_drop]
  have htail : tail.length = i := by simp only [tail,List.length_drop,ix]; omega
  have haddr : L.address j i = a := by
    apply Fin.ext
    rw [L.address_val _ (hi.le.trans (fit j))]
    dsimp [i]; omega
  have val := contents j _ _ _ he
  rw [htail,haddr] at val
  rw [readCell,dite_eq_left hwritten]
  change some (encodeBit w ((s j).reverse[i]'(by simpa using hi))) = _
  rw [List.getElem_reverse]
  exact congrArg some val.symm

/-- The exact updated memory follows from physical occupancy and the frame.
The right side is a function of the old memory and the logical stack bank. -/
theorem memory_eq (old new : Word w → Word w) (contents : L.Contents new s)
    (fit : ∀ j, (s j).length ≤ L.capacity)
    (frame : ∀ a, (∀ j, a.val < L.base j ∨ L.base j + (s j).length ≤ a.val) → new a = old a) :
    new = memory L s old := by
  funext a
  by_cases h : ∃ j, occupies L s a j
  · rw [memory,readCell_value L s new contents fit a h]; rfl
  · rw [memory,readCell,dite_eq_right h]
    exact frame a fun j => by have := not_exists.mp h j; unfold occupies at this; omega

/-- Apply stack initialization to the saved DFS scratch by replacing its occupied cells with
encoded stack bits. -/
noncomputable def scratch {endAddr : ℕ} (saved : DFS.Scratch w endAddr) : DFS.Scratch w endAddr :=
  fun a => (readCell L s a.val).getD (saved a)

theorem scratch_memory (endAddr : ℕ) (old : Word w → Word w) :
    DFS.scratch endAddr (memory L s old) = scratch L s (DFS.scratch endAddr old) := rfl

section Site

variable {d e k r : ℕ}

/-- The leaf startup port that supplies the serialized incident data to the virtual site
processor. -/
def incidentPort (r k : ℕ) : LeafStartup.Port r k :=
  SiteProcessorPorts.pub r (LeafStartup.expr k) ProcessorPublic.incidentPort

/-- The finite source decoder designates precisely one incident port. -/
theorem field_incident_iff (j : LeafStartup.Port r k) :
    LeafStartup.field j = .incident ↔ j = incidentPort r k := by
  constructor
  · intro h
    unfold LeafStartup.field at h
    split at h <;> first | contradiction | rfl
  · rintro rfl; rfl

theorem install_incident (x : VirtualSite.Input d e w) (args : Fin k → Word w) :
    Function.update (scalarBank (LeafStartup.field (r := r)) x args) (incidentPort r k)
      (List.ofFn (RAMLayout.incidentBits x.sends x.v)) = LeafStartup.bank r x args := by
  funext j
  by_cases hj : j = incidentPort r k
  · subst j; rw [Function.update_self]; rfl
  · rw [Function.update_of_ne hj]
    change fieldBits x args (scalarField (LeafStartup.field j)) = _
    rw [scalarField,ite_eq_right (mt (field_incident_iff j).mp hj)]
    rfl

end Site
end PairSimulation.LeafLoadedBank

end VPVNP
end Computability
end OAI

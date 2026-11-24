import OAI.Computability.VPVNP.RAMProcessorCreditPorts

/-!
# Incrementing a probe ordinal after recording it

The timestamp field of a probe is the ordinal before this increment. The
routine scans the ordinal word and scratch stack. It returns with the
incremented ordinal, or reaches the rejecting halt on overflow.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.CallCredit

open BurstRAM TapeWord

/-- The incrementer's active word is the ordinal. Its other labels are
injected into the usual budget ports. -/
def ordinalPorts : Charges.Port → Port
  | .cost => .ordinal
  | p => .budget p

theorem ordinalPorts_injective : Function.Injective ordinalPorts := by
  intro i j h
  cases i <;> cases j <;> simp_all [ordinalPorts]

/-- Increment the probe ordinal after emitting its old value as the timestamp. Overflow of the
fixed-width word leads to rejection. -/
def finishProbe : FiniteRoutine Port := Charges.routine ordinalPorts (.scan true true)

private theorem ordinalFrame (s : Stacks Port) (bits : List Bool) (ht : s (.budget .tmp) = []) :
    installStacks ordinalPorts s
      (Charges.scanData true (s (.budget .fuel)) (s (.budget .call)) (s (.budget .site))
        (s (.budget .globalLeft)) bits []).stacks = Function.update s .ordinal bits := by
  apply installStacks_frame ordinalPorts_injective
  · intro p
    cases p <;> simp [ordinalPorts, Charges.scanData, Charges.Data.stacks, ht]
  · intro p hp
    exact Function.update_of_ne (fun h => hp .cost h.symm) ..

/-- Increment only the ordinal after its old value has been emitted. -/
theorem finishProbe_run {w : ℕ} (o : Word w) (ho : o.val + 1 < 2 ^ w) (s : Stacks Port)
    (hs : s .ordinal = wordBits o) (ht : s (.budget .tmp) = []) :
    finishProbe.Runs (4*w+2) s
      (Function.update s .ordinal (wordBits (⟨o.val + 1, ho⟩ : Word w))) := by
  have h := Charges.adjustRun true true (wordBits o)
    (s (.budget .fuel)) (s (.budget .call)) (s (.budget .site)) (s (.budget .globalLeft))
  simp only [length_wordBits, Charges.adjust_inc_word o ho] at h
  have hh := Charges.liftRun ordinalPorts_injective s
    (entry := .scan true true) (exit := .done) (by decide) h
  simp only [ordinalFrame s _ ht, ↓reduceIte] at hh
  rw [← hs, Function.update_eq_self] at hh
  exact hh

/-- Overflow reaches the rejecting row after exactly the same fixed-width
scan. It makes no further probe or program choice. -/
theorem finishProbe_reject {w : ℕ} (o : Word w) (ho : 2 ^ w ≤ o.val + 1) (s : Stacks Port)
    (hs : s .ordinal = wordBits o) (ht : s (.budget .tmp) = []) :
    ∃ out, StackRuns finishProbe.body.standalone (4*w+2) (some (.scan true true)) s
      (some .reject) out := by
  have hf := (Charges.adjust_overflow_iff (wordBits o)).mpr (by simpa only [length_wordBits, value_wordBits] using ho)
  have h := Charges.adjustRun true true (wordBits o)
    (s (.budget .fuel)) (s (.budget .call)) (s (.budget .site)) (s (.budget .globalLeft))
  simp only [length_wordBits, hf] at h
  have hh := Charges.liftRun ordinalPorts_injective s
    (entry := .scan true true) (exit := .reject) (by decide) h
  simp only [ordinalFrame s _ ht, show Charges.State.reject ≠ .done by decide, ↓reduceIte] at hh
  rw [← hs, Function.update_eq_self] at hh
  exact ⟨_, hh⟩

end RAMTape.CallCredit

end VPVNP
end Computability
end OAI

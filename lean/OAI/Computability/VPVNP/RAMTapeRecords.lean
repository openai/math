import OAI.Computability.VPVNP.RAMTapeRecordWord
import OAI.Computability.VPVNP.RAMTapeSuccessorFields
import Mathlib.Data.List.FinRange

/-!
# Fixed control for emitting a whole five-word RAM probe record

The call interpreter stages the tag, address, value, call start and probe
ordinal in five word stacks. Each emission takes one free slot, copies all
five words in order, and restores the caller's registers. The empty and
malformed remaining-slot counters reject without continuing.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.RecordBuffer

open BurstRAM RAMSerialization

private def putFields : List (Fin 5) → FiniteRoutine Port
  | [] => .ret
  | j :: js => (appendWord (.field j)).followedBy (putFields js)

private def words (s : Stacks Port) (js : List (Fin 5)) : List Bool := js.flatMap (fun j => s (.field j))

private theorem putFields_run (js : List (Fin 5)) (s : Stacks Port) (w : ℕ)
    (ht : s .temp = []) (hf : ∀ j ∈ js, (s (.field j)).length = w) :
    (putFields js).Runs (js.length*(5*w+2)+1) s
      (Function.update s .reverseBuffer ((words s js).reverse ++ s .reverseBuffer)) := by
  induction js generalizing s with
  | nil => simpa [putFields, FiniteRoutine.ret, words, FiniteRoutine.Runs, FiniteRoutine.ofRoutine] using Routine.runs_ret s
  | cons j js ih =>
    let mid := Function.update s .reverseBuffer ((s (.field j)).reverse ++ s .reverseBuffer)
    have h₁ : (appendWord (.field j)).Runs (5*w+2) s mid := by
      simpa only [mid, hf j (List.mem_cons_self ..)] using
        appendWord_run (src := .field j) (by simp) (by simp) s ht
    have h₂ := ih mid (by simpa [mid] using ht) (fun i hi => by
      simpa [mid] using hf i (List.mem_cons_of_mem _ hi))
    have he : words mid js = words s js := by simp [words, mid]
    have hh := h₁.followedBy h₂
    rw [he] at hh
    rw [show 5*w+2+(js.length*(5*w+2)+1) = (js.length+1)*(5*w+2)+1 by ring] at hh
    simpa only [putFields, mid, Function.update_self, Function.update_idem, words, List.flatMap_cons,
      List.reverse_append, List.append_assoc, List.length_cons] using hh

/-- The one-record callback. The tag selects initialization, read or write
and all fields already occupy the paper's fixed word width. -/
def appendRecord : FiniteRoutine Port := .ofRoutine
  (Routine.popCase Port.remaining (Routine.halt false) (Routine.halt false)
    (putFields (List.finRange 5)).body)

/-- Bank after record emission, with the new free-slot tally and the reversed record encoding
prepended to the buffer. -/
def emitted (s : Stacks Port) (left encoded : List Bool) : Stacks Port :=
  Function.update (Function.update s .remaining left) .reverseBuffer (encoded.reverse ++ s .reverseBuffer)

/-- Staging canonical record words in the five registers produces precisely
the bits of the paper's physical slot, with no fresh choices. -/
theorem appendRecord_run {w : ℕ} (hw : 2 ≤ w) (record : Option (WordRecord w))
    (s : Stacks Port) (left : List Bool) (hleft : s .remaining = true::left)
    (ht : s .temp = []) (hf : ∀ j, s (.field j) = BurstRAM.wordBits ((recordFormat hw).words record j)) :
    appendRecord.Runs (25*w+12) s
      (emitted s left (List.ofFn ((recordFormat hw).encode record))) := by
  let next := Function.update s Port.remaining left
  have hwords (j : Fin 5) : next (.field j) = BurstRAM.wordBits ((recordFormat hw).words record j) := by
    simpa [next] using hf j
  have h := putFields_run (List.finRange 5) next w (by simpa [next] using ht)
    (fun j _ => by rw [hwords, length_wordBits])
  have he : words next (List.finRange 5) = List.ofFn ((recordFormat hw).encode record) := by
    rw [SuccessorFields.raw_eq_flatten_words, Format.encode, Equiv.symm_apply_apply]
    unfold words
    rw [List.flatMap_def, List.ofFn_eq_map]
    simp only [hwords]
  rw [he] at h
  have hr := Routine.runs_popCase_true Port.remaining (Routine.halt false) (Routine.halt false)
    (putFields (List.finRange 5)).body hleft h
  rw [List.length_finRange, show 5*(5*w+2)+1+1=25*w+12 by ring] at hr
  simpa only [appendRecord, FiniteRoutine.ofRoutine, FiniteRoutine.Runs, emitted, next,
    Function.update_of_ne (by decide : Port.reverseBuffer ≠ Port.remaining)] using hr

end RAMTape.RecordBuffer

end VPVNP
end Computability
end OAI

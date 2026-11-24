import OAI.Computability.VPVNP.RAMTapeInputFields
import OAI.Computability.VPVNP.RAMTapeInputRoutines
import OAI.Computability.VPVNP.RAMSiteInput

/-!
# Uniform finite-stack parsing of the physical site tape

After the public field lengths are available as unary scratch counters, the
control copies the self-delimiting prefix, the site address, its four header
bits and the whole incident vector, then consumes the zero padding. The control
and its register set are fixed across all lengths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputReader

open BurstRAM ProcessorInput RAMLayout RAMSerialization UniversalMachine

private def headerMarks :=
  let mark := Routine.push InputPort.count true
  ((mark.followedBy mark).followedBy mark).followedBy mark

private theorem headerMarks_runs (s : Stacks InputPort) :
    headerMarks.Runs 4 s (Function.update s .count (List.replicate 4 true ++ s .count)) := by
  let push := fun t : Stacks InputPort => Function.update t .count (true :: t .count)
  have one (t : Stacks InputPort) : (Routine.push .count true).Runs 1 t (push t) :=
    Routine.runs_push ..
  have h := (((one s).followedBy (one (push s))).followedBy (one (push (push s)))).followedBy
    (one (push (push (push s))))
  have he : push (push (push (push s))) = Function.update s .count (List.replicate 4 true ++ s .count) := by
    simp [push, Function.update_idem, List.replicate_succ]
  exact he ▸ h

/-- Sequential reader. The address and incident lengths are popped from their
own counters and the fixed four header marks are written by the control. -/
def parse := (((((prefixRoutine.followedBy (readField .address)).followedBy headerMarks).followedBy
  (readField .header)).followedBy (readField .incident)).followedBy padding)

/-- Bank after parsing, with the prefix, address, header, and incident bits on separate stacks
and the measured size preserved. -/
def result (s : Stacks InputPort) (pref addr hdr inc : List Bool) : Stacks InputPort
  | .input | .tmp | .count | .addressCount | .incidentCount => []
  | .prefix => pref
  | .address => addr
  | .header => hdr
  | .incident => inc
  | .size => s .size

/-- Correct on all data-field values and all lengths of zero padding. Unused
scratch data are cleared, while the full literal prefix is saved in order. -/
theorem parse_runs (s : Stacks InputPort) (table addr hdr inc : List Bool) (z : ℕ)
    (hlen : hdr.length = 4)
    (hin : s .input = (unary table.length ++ table) ++ (addr ++ hdr ++ inc ++ List.replicate z false))
    (ht : s .tmp = []) (hc : s .count = []) (hp : s .prefix = [])
    (ha : s .address = []) (hh : s .header = []) (hi : s .incident = [])
    (hac : s .addressCount = List.replicate addr.length true)
    (hic : s .incidentCount = List.replicate inc.length true) :
    parse.Runs (10*table.length + 5*addr.length + 5*hdr.length + 5*inc.length + 2*z + 17) s
      (result s (unary table.length ++ table) addr hdr inc) := by
  let pref := unary table.length ++ table
  let pad := List.replicate z false
  let u := Function.update (Function.update s .input (addr ++ hdr ++ inc ++ pad)) .prefix pref
  let a := fieldResult u .address addr (hdr ++ inc ++ pad)
  let m := Function.update a .count (List.replicate 4 true ++ a .count)
  let b := fieldResult m .header hdr (inc ++ pad)
  let c := fieldResult b .incident inc pad
  have h₁ := prefixRoutine_runs s table (addr ++ hdr ++ inc ++ pad) hin ht hc hp
  change prefixRoutine.Runs _ s u at h₁
  have h₂ : (readField .address).Runs _ u a := readField_runs u .address addr (hdr ++ inc ++ pad)
    (by simp [u, List.append_assoc]) (by simpa [u, Field.counter] using hac) (by simpa [u] using ht)
  have h₃ := headerMarks_runs a
  change headerMarks.Runs 4 a m at h₃
  have h₄ : (readField .header).Runs _ m b := readField_runs m .header hdr (inc ++ pad)
    (by simp [m, a, fieldResult, Field.counter, Field.output, List.append_assoc])
    (by simp [m, a, u, fieldResult, Field.counter, Field.output, hc, hlen])
    (by simp [m, a, u, fieldResult, Field.counter, Field.output, ht])
  have h₅ : (readField .incident).Runs _ b c := readField_runs b .incident inc pad
    (by simp [b, fieldResult, Field.counter, Field.output])
    (by simp [b, m, a, u, fieldResult, Field.counter, Field.output, hic])
    (by simp [b, m, a, u, fieldResult, Field.counter, Field.output, ht])
  have h₆ := padding_runs c z (by simp [c, fieldResult, Field.counter, Field.output, pad])
  have he : Function.update c .input [] = result s pref addr hdr inc := by
    funext j
    cases j <;> simp [c, b, m, a, u, fieldResult, Field.counter, Field.output, result, ha, hh, hi, ht]
  rw [he] at h₆
  have run := ((((h₁.followedBy h₂).followedBy h₃).followedBy h₄).followedBy h₅).followedBy h₆
  exact (show 10*table.length+6 + (5*addr.length+2) + 4 + (5*hdr.length+2) + (5*inc.length+2) +
    (2*z+1) = 10*table.length + 5*addr.length + 5*hdr.length + 5*inc.length + 2*z + 17 by omega) ▸ run

/-- The local parser begins with its entire tape at the input head. The size
and field counts can have been produced by previous routines on these stacks. -/
def prepared (raw : List Bool) (d width : ℕ) (size : List Bool) : Stacks InputPort
  | .input => raw
  | .addressCount => List.replicate d true
  | .incidentCount => List.replicate width true
  | .size => size
  | _ => []

/-- A linear stack-instruction bound for parsing the literal physical tape.
The successful run exposes the exact incident vector used by the word machine. -/
theorem parse_processorTape {d H w : ℕ} (program : UniversalMachine.Program) (n : ℕ)
    (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool) (size : List Bool)
    (hfit : Fits program n d H w) :
    let s := prepared (ProcessorInput.tape program n v hdr inc) d (width d H w) size
    ∃ t ≤ 5*n+17, parse.Runs t s (result s (programPrefix program)
      (List.ofFn (RAMSerialization.wordBits d v)) (List.ofFn hdr) (List.ofFn inc)) := by
  let s := prepared (ProcessorInput.tape program n v hdr inc) d (width d H w) size
  let t := tableBits program
  let a := List.ofFn (RAMSerialization.wordBits d v)
  let h := List.ofFn hdr
  let c := List.ofFn inc
  let z := n - ((programPrefix program).length + (d+4+width d H w))
  have run := parse_runs s t a h c z (List.length_ofFn)
    (by simp only [s, prepared, ProcessorInput.tape, ProcessorInput.payload, programPrefix, t, a, h, c, z,
      List.append_assoc]) rfl rfl rfl rfl rfl rfl (by simp [s, prepared, a]) (by simp [s, prepared, c])
  refine ⟨_, ?_, run⟩
  have hpre : (programPrefix program).length = 2*t.length+1 := by
    simp [programPrefix, unary, t]; omega
  have hf : (programPrefix program).length + (d+4+width d H w) ≤ n := hfit
  dsimp only [a, h, c, z]
  simp only [List.length_ofFn]
  omega

end RAMTape.InputReader

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.RAMTapeInputRoutines
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.EvaluatorInputBank
import OAI.Computability.VPVNP.AffinePinIndex

/-! # Public field lengths in the processor literal

The first bits of a processor's literal are its own self-delimiting machine table. The
two cut lengths follow in compact binary fields. The parser reads the parameters on a
copy of the tape. Its original bit stream, including the machine's complete prefix and
the public length fields themselves, remains available for time-zero memory initialization.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInput

open VPVNP RAMTape InputReader SuccessorFields

/-- Named stacks for the full original input, its separate parameter-reader copy, and
the bit-to-tally decoder. Each destination counter is a distinct input-cutter port. -/
inductive Port
  | cut (p : InputPort)
  | peek (p : InputPort)
  | bits | high | scratch
  deriving DecidableEq, Fintype

/-- The binary counts specify the input-memory and physical routing lengths. -/
inductive LengthField | memory | routing
  deriving DecidableEq

/-- The public unary counter obtained after decoding a length parameter. -/
def counter : LengthField → Port
  | .memory => .cut .count
  | .routing => .cut .incidentCount

private def readPorts : Option Unit → Port
  | none => .peek .input
  | some _ => .bits

private def decodePorts (f : LengthField) : AffinePin.Index.Port → Port
  | .bits => .bits
  | .high => .high
  | .index => counter f
  | .tmp => .scratch

/-- Read one tagged binary public length and expand its little-endian bits into a unary
count. The large unary count exists only on work stacks. -/
def readLength (f : LengthField) : FiniteRoutine Port :=
  ((FiniteRoutine.ofRoutine (Evaluator.InputBank.readField ())).onPorts readPorts).followedBy
    (AffinePin.Index.decode.onPorts (decodePorts f))

/-- Scratch fields are empty on entry. The public length's tagged bits are consumed only
from the peek stack, leaving the original input untouched. -/
theorem readLength_runs (f : LengthField) (s : Stacks Port) (bs tail : List Bool)
    (hin : s (.peek .input) = Evaluator.InputBank.fieldBits bs ++ tail)
    (hb : s .bits = []) (hh : s .high = []) (hs : s .scratch = []) (hc : s (counter f) = []) :
    ∃ t ≤ 7*TapeWord.value bs + 9*bs.length+3, (readLength f).Runs t s
      (Function.update (Function.update s (.peek .input) tail) (counter f)
        (List.replicate (TapeWord.value bs) true)) := by
  let u := Function.update (Function.update s (.peek .input) tail) Port.bits bs
  let z := Function.update (Function.update s (.peek .input) tail) (counter f) (List.replicate (TapeWord.value bs) true)
  have raw := Evaluator.InputBank.readField_runs () bs tail (fun _ => [])
  have r : ((FiniteRoutine.ofRoutine (Evaluator.InputBank.readField ())).onPorts readPorts).Runs
      (3*bs.length+1) s u := by
    apply (FiniteRoutine.ofRoutine (Evaluator.InputBank.readField ())).runs_onPorts_framed
      (by decide : Function.Injective readPorts) raw
    · intro k; cases k <;> first | exact hin | exact hb
    · intro k; cases k <;> simp [readPorts, u, Evaluator.InputBank.frame]
    · intro k hk
      have h₁ : k ≠ .peek .input := fun e => hk none e.symm
      have h₂ : k ≠ .bits := fun e => hk (some ()) e.symm
      simp [u, h₁, h₂]
  obtain ⟨t, ht, dec⟩ := AffinePin.Index.decode_runs bs
  have hd : (AffinePin.Index.decode.onPorts (decodePorts f)).Runs t u z := by
    apply AffinePin.Index.decode.runs_onPorts_framed
      (by cases f <;> decide : Function.Injective (decodePorts f)) dec
    · intro k; cases k <;> cases f <;> simp_all [u, decodePorts, counter, AffinePin.Index.bank]
    · intro k; cases k <;> cases f <;> simp_all [z, decodePorts, counter, AffinePin.Index.bank]
    · intro k hk
      have h₁ : k ≠ .bits := fun e => hk .bits e.symm
      have h₂ : k ≠ counter f := fun e => hk .index e.symm
      simp [z, u, h₁, h₂]
  exact ⟨_, by omega, r.followedBy hd⟩

private def copyInput : FiniteRoutine Port :=
  prependCopy (.cut .input) (.peek .input) .scratch

private def readPrefix : FiniteRoutine Port :=
  (FiniteRoutine.ofRoutine InputReader.prefixRoutine).onPorts Port.peek

/-- Look at the machine table, then read both length parameters. -/
def header : FiniteRoutine Port :=
  (copyInput.followedBy readPrefix).followedBy ((readLength .memory).followedBy (readLength .routing))

/-- The two tagged binary fields follow the prefix and are themselves part of the literal. -/
def parameters (memory routing : List Bool) : List Bool :=
  Evaluator.InputBank.fieldBits memory ++ Evaluator.InputBank.fieldBits routing

/-- Input bank before any tape bit is consumed. -/
def initial (raw : List Bool) : Stacks Port
  | .cut .input => raw
  | _ => []

/-- Retained raw tape and parsed counters. The peek and prefix stacks also preserve the
public parser's remaining data, allowing another fixed public field to be read later. -/
def prepared (raw savedPrefix rest : List Bool) (mem inc : ℕ) : Stacks Port
  | .cut .input => raw
  | .peek .input => rest
  | .peek .prefix => savedPrefix
  | .cut .count => List.replicate mem true
  | .cut .incidentCount => List.replicate inc true
  | _ => []

/-- The finite table starts on the unmodified whole input. Its running time is linear in
the input length, the tagged binary lengths, and the two decoded numerical values. -/
theorem header_runs (table mem inc rest : List Bool) :
    let pref := UniversalMachine.unary table.length ++ table
    let raw := pref ++ parameters mem inc ++ rest
    ∃ t ≤ 5*raw.length + 10*table.length + 7*(TapeWord.value mem + TapeWord.value inc) +
      9*(mem.length+inc.length) + 14, header.Runs t (initial raw)
      (prepared raw pref rest (TapeWord.value mem) (TapeWord.value inc)) := by
  intro pref raw
  let s := Function.update (initial raw) (.peek .input) raw
  let u := Function.update (Function.update s (.peek .input) (parameters mem inc ++ rest)) (.peek .prefix) pref
  let z := Function.update (Function.update u (.peek .input) (Evaluator.InputBank.fieldBits inc ++ rest))
    (counter .memory) (List.replicate (TapeWord.value mem) true)
  have c : copyInput.Runs (5*raw.length+2) (initial raw) s := by
    have h := prependCopy_runs (Port.cut .input) (.peek .input) .scratch
      (by decide) (by decide) (by decide) (initial raw) rfl
    simpa [copyInput, initial, s] using h
  have p : readPrefix.Runs (10*table.length+6) s u := by
    have src := InputReader.prefixRoutine_runs (s ∘ Port.peek) table (parameters mem inc ++ rest)
      (by simp [s, raw, pref, List.append_assoc]) rfl rfl rfl
    apply (FiniteRoutine.ofRoutine InputReader.prefixRoutine).runs_onPorts_framed
      (by decide : Function.Injective Port.peek) src
    · exact fun _ => rfl
    · intro k; cases k <;> rfl
    · intro k hk
      simp [u, Function.update_of_ne (fun e => hk .input e.symm), Function.update_of_ne (fun e => hk .prefix e.symm)]
  obtain ⟨t₁, ht₁, a⟩ := readLength_runs .memory u mem (Evaluator.InputBank.fieldBits inc ++ rest)
    (by simp [u, parameters, List.append_assoc]) rfl rfl rfl rfl
  obtain ⟨t₂, ht₂, b⟩ := readLength_runs .routing z inc rest rfl rfl rfl rfl rfl
  have out : Function.update (Function.update z (.peek .input) rest) (counter .routing)
        (List.replicate (TapeWord.value inc) true) =
      prepared raw pref rest (TapeWord.value mem) (TapeWord.value inc) := by
    funext k; rcases k with k | k | _ | _ | _ <;> first | cases k <;> rfl | rfl
  rw [out] at b
  refine ⟨_, by omega, (c.followedBy p).followedBy (a.followedBy b)⟩

end TeamTapeInput

end BorderVNP
end Computability
end OAI

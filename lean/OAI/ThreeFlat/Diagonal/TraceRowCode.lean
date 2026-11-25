import OAI.ThreeFlat.Diagonal.TraceBankExecution
import OAI.ThreeFlat.Diagonal.TraceRows
import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Canonical local bits for the CPU row

A fixed header has five words: instruction tag, program counter, persistent
state, probe address, and probe payload or returned value. The register file
follows the header. Unused fields have one encoding.
-/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization TraceBanks

variable {w p r : ℕ}

def tagWord (h : 3 ≤ w+1) (t : Fin 8) : Word (w+1) :=
  ⟨t.val, lt_of_lt_of_le t.isLt (show 8 ≤ 2 ^ (w+1) from Nat.pow_le_pow_right (by decide : 0 < 2) h)⟩

def pcWord (hp : p ≤ 2 ^ (w+1)) (i : Fin p) : Word (w+1) := i.castLE hp

def header (h : 3 ≤ w+1) (hp : p ≤ 2 ^ (w+1))
    (rows : Row (w+1) (Snapshot w p r)) : Fin 5 → Word (w+1) :=
  let active (s : Snapshot w p r) (t : Fin 8) (a v : Word (w+1)) :=
    ![tagWord h t, pcWord hp s.pc, wide s.persistent, a, v]
  match rows with
  | .pad => fun _ => 0
  | .halt s none => active s 6 0 0
  | .halt s (some v) => active s 7 0 v
  | .move s .tick => active s 1 0 0
  | .move s (.choice false) => active s 2 0 0
  | .move s (.choice true) => active s 3 0 0
  | .move s (.read a v) => active s 4 a v
  | .move s (.write a v) => active s 5 a v

def regs : Row (w+1) (Snapshot w p r) → Fin r → Word (w+1)
  | .move s _ | .halt s _ => wide ∘ s.reg
  | .pad => fun _ => 0

def packedWords (h : 3 ≤ w+1) (hp : p ≤ 2 ^ (w+1)) (row : Row (w+1) (Snapshot w p r)) :
    Fin (5+r) → Word (w+1) := Fin.append (header h hp row) (regs row)

private def parseRow (data : Fin (5+r) → Word (w+1)) : Row (w+1) (Snapshot w p r) :=
  let hd (j : Fin 5) := data (j.castAdd r)
  if bound : (hd 1).val < p then
    let s : Snapshot w p r :=
      ⟨⟨(hd 1).val, bound⟩, narrow (hd 2), fun i => narrow (data (Fin.natAdd 5 i))⟩
    match (hd 0).val with
    | 1 => .move s .tick
    | 2 => .move s (.choice false)
    | 3 => .move s (.choice true)
    | 4 => .move s (.read (hd 3) (hd 4))
    | 5 => .move s (.write (hd 3) (hd 4))
    | 6 => .halt s none
    | 7 => .halt s (some (hd 4))
    | _ => .pad
  else .pad

private theorem parse_packed (h : 3 ≤ w+1) (hp : p ≤ 2 ^ (w+1)) (row : Row (w+1) (Snapshot w p r)) :
    parseRow (packedWords h hp row) = row := by
  cases row with
  | pad =>
    simp [parseRow, packedWords, header]
  | halt s out =>
    obtain ⟨pc,persistent,reg⟩ := s
    cases out <;> simp [parseRow, packedWords, header, regs, tagWord, pcWord, pc.isLt, Function.comp_def]
  | move s e =>
    obtain ⟨pc,persistent,reg⟩ := s
    cases e with
    | choice b => cases b <;> simp [parseRow, packedWords, header, regs, tagWord, pcWord, pc.isLt, Function.comp_def]
    | tick | read | write => simp [parseRow, packedWords, header, regs, tagWord, pcWord, pc.isLt, Function.comp_def]

/-- The accepting word format has exactly five overhead words in addition
to the register file. Its canonical decoder rejects every extra bit pattern. -/
def rowFormat (h : 3 ≤ w+1) (hp : p ≤ 2 ^ (w+1)) :
    Format (w+1) (5+r) (Row (w+1) (Snapshot w p r)) where
  words := packedWords h hp
  parse := parseRow
  parse_words := parse_packed h hp

@[simp] theorem rowFormat_header (h : 3 ≤ w+1) (hp : p ≤ 2 ^ (w+1))
    (x : Row (w+1) (Snapshot w p r)) (j : Fin 5) :
    (rowFormat h hp).words x (j.castAdd r) = header h hp x j := by simp [rowFormat, packedWords]

@[simp] theorem rowFormat_reg (h : 3 ≤ w+1) (hp : p ≤ 2 ^ (w+1))
    (x : Row (w+1) (Snapshot w p r)) (j : Fin r) :
    (rowFormat h hp).words x (Fin.natAdd 5 j) = regs x j := by simp [rowFormat, packedWords]

/-- A complete array of CPU rows occupies exactly the fixed row width
times the number of physical steps. -/
def traceFormat (h : 3 ≤ w+1) (hp : p ≤ 2 ^ (w+1)) (f : ℕ) :
    Format (w+1) (f*(5+r)) (Fin f → Row (w+1) (Snapshot w p r)) :=
  (rowFormat h hp).replicate f

end ThreeFlat.Diagonal.TraceRows

end OAI

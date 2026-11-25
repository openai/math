import OAI.Computability.BorderVNP.TeamTapeInput
import OAI.Computability.BorderVNP.TeamTapeInputEmit
import Mathlib.Data.Nat.Log

/-! # Staging a full processor literal and its routing fields

Both cut lengths fit in `⌈log₂(n+1)⌉` bits at processor length `n`. The parser recovers
the complete prescribed memory segment, including its own program prefix and both length
fields. A following finite table emits exactly two canonical physical slots for each input
bit. Its named-port embedding retains all private parser state and the independent interior
routing bytes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInput

open VPVNP BurstRAM RAMTape RAMSerialization

/-- Public lengths occupy a fixed compact binary width determined by the processor input length. -/
def digits (n m : ℕ) : List Bool :=
  BurstRAM.wordBits (Fin.ofNat (2^(Nat.clog 2 (n+1))) m)

theorem digits_value {n m : ℕ} (hm : m ≤ n) : TapeWord.value (digits n m) = m := by
  simp only [digits, TapeWord.value_wordBits, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt ((Nat.lt_succ_of_le hm).trans_le (Nat.le_pow_clog (by decide) _))

/-- Bit count including both delimiters in the pinned compact length fields. -/
theorem length_parameters (n m i : ℕ) :
    (parameters (digits n m) (digits n i)).length = 4*Nat.clog 2 (n+1)+2 := by
  simp [parameters, digits, Evaluator.InputBank.length_fieldBits]
  omega

/-- The complete length-`n` tape, with a literal of length `t₀`, free residual literal
bits, exterior and pin data, routing input and canonical trailing zeros. -/
theorem run_layout (p : UniversalMachine.Program) (n t₀ : ℕ)
    (free pins routing : List Bool) (exterior : List (List Bool))
    (hf : (UniversalMachine.programPrefix p).length + 4*Nat.clog 2 (n+1)+2+free.length = t₀)
    (hsize : t₀+exterior.flatten.length+pins.length+routing.length ≤ n) :
    let m := t₀+exterior.flatten.length+pins.length
    let publicBits := parameters (digits n m) (digits n routing.length)
    let literal := UniversalMachine.programPrefix p ++ publicBits ++ free
    let data := inputData literal exterior pins
    let padding := List.replicate (n-(m+routing.length)) false
    let raw := data ++ routing ++ padding
    raw.length = n ∧ literal.length = t₀ ∧ ∃ t ≤ 46*n+19,
      program.Runs t (initial raw)
        (loaded (UniversalMachine.programPrefix p) (free ++ exterior.flatten ++ pins ++ routing ++ padding) data routing) := by
  intro m publicBits literal data pad raw
  have hl : literal.length = t₀ := by simpa [literal, publicBits, length_parameters, Nat.add_assoc] using hf
  have hd : data.length = m := by simp [data, inputData, hl, m, Nat.add_assoc]
  have hr : raw.length = n := by simp only [raw, List.length_append, hd, pad, List.length_replicate]; omega
  have hm : TapeWord.value (digits n m) = data.length := (digits_value (by dsimp [m]; omega)).trans hd.symm
  have hi := digits_value (show routing.length ≤ n by omega)
  obtain ⟨t, ht, htape⟩ := runs (UniversalMachine.tableBits p) (digits n m) (digits n routing.length)
    free pins routing exterior (n-(m+routing.length)) hm hi
  have htab : (UniversalMachine.tableBits p).length ≤ n := by
    have hh : (UniversalMachine.tableBits p).length ≤ (UniversalMachine.programPrefix p).length := by
      simp [UniversalMachine.programPrefix]
    omega
  have hbits : Nat.clog 2 (n+1) ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n))
  change t ≤ 5*raw.length + 10*(UniversalMachine.tableBits p).length + 12*(data.length+routing.length) +
    9*((digits n m).length+(digits n routing.length).length) + 2*(n-(m+routing.length)) + 19 at ht
  simp only [digits, length_wordBits, hr, hd] at ht
  exact ⟨hr, hl, t, by dsimp [m] at *; omega, htape⟩

/-- Processor ports for the input parser and the physical record emitter. -/
abbrev InitPort := Port ⊕ TeamTapeInputEmit.Port

/-- The emitter consumes the actual extracted header. Its other ports hold the staged
address cursor and the growing physical sorting buffer. -/
def emitPort : TeamTapeInputEmit.Port → InitPort
  | .bits => .inl (.cut .header)
  | k => .inr k

private theorem emitPort_inj : Function.Injective emitPort := by
  intro i j h
  cases i <;> cases j <;> simp_all [emitPort]

/-- The joined fixed input splitter and initialization-pair emitter. -/
def parserAndEmitter : FiniteRoutine InitPort :=
  (program.onPorts Sum.inl).followedBy (TeamTapeInputEmit.program.onPorts emitPort)

/-- A staged record buffer and cursor suffice on entry; the emitter's bit port is wired
directly to the output of the parser. Each initialization record is then appended and
the interior routing stack is kept bit for bit. -/
theorem initialize_runs {w H a : ℕ} (hw : 2 ≤ w) (p : UniversalMachine.Program) (n t₀ : ℕ)
    (free pins routing : List Bool) (exterior : List (List Bool))
    (hf : (UniversalMachine.programPrefix p).length + 4*Nat.clog 2 (n+1)+2+free.length = t₀)
    (hsize : t₀+exterior.flatten.length+pins.length+routing.length ≤ n)
    (s : Stacks TeamTapeInputEmit.Port) (rs : List (WordRecord w))
    (ready : TeamTapeInputEmit.Ready hw H a [] rs s) :
    let m := t₀+exterior.flatten.length+pins.length
    let publicBits := parameters (digits n m) (digits n routing.length)
    let literal := UniversalMachine.programPrefix p ++ publicBits ++ free
    let data := inputData literal exterior pins
    let padding := List.replicate (n-(m+routing.length)) false
    let raw := data ++ routing ++ padding
    2*(a+data.length) ≤ 2^w → rs.length+2*data.length ≤ 4*H →
      ∃ t out, t ≤ 46*n+19 + TeamTapeInputEmit.budget w data.length ∧
        parserAndEmitter.Runs t (Sum.elim (initial raw) s) out ∧
        TeamTapeInputEmit.Ready hw H (a+data.length) []
          (rs ++ TeamTapeInputEmit.records w a data) (out ∘ emitPort) ∧
        out (.inl (.cut .incident)) = routing := by
  intro m publicBits literal data pad raw fits cap
  obtain ⟨_, _, t, ht, hr⟩ := run_layout p n t₀ free pins routing exterior hf hsize
  let u := loaded (UniversalMachine.programPrefix p) (free ++ exterior.flatten ++ pins ++ routing ++ pad) data routing
  let mid : Stacks InitPort := Sum.elim u s
  have parse : (program.onPorts Sum.inl).Runs t (Sum.elim (initial raw) s) mid := by
    apply program.runs_onPorts_framed Sum.inl_injective hr
    · exact fun _ => rfl
    · exact fun _ => rfl
    · rintro (k | k) hk
      · exact (hk k rfl).elim
      · rfl
  have r : TeamTapeInputEmit.Ready hw H a data rs (mid ∘ emitPort) :=
    ⟨rfl, ready.cursor, ready.buffer, ready.fields⟩
  obtain ⟨k, v, hk, hrun, hout⟩ := TeamTapeInputEmit.runs r fits cap
  let out := installStacks emitPort mid v
  have hstart : installStacks emitPort mid (mid ∘ emitPort) = mid :=
    installStacks_eq emitPort_inj mid _ (fun _ => rfl)
  have emit := TeamTapeInputEmit.program.runs_onPorts emitPort_inj mid hrun
  rw [hstart] at emit
  have he : out ∘ emitPort = v := funext fun k => installStacks_at emitPort_inj mid v k
  exact ⟨_, out, Nat.add_le_add ht hk, parse.followedBy emit, he ▸ hout,
    installStacks_outside mid v (fun k => by cases k <;> simp [emitPort])⟩

end TeamTapeInput

end BorderVNP
end Computability
end OAI

import OAI.Computability.VPVNP.PrimedInputRAMLayout
import OAI.Computability.VPVNP.RAMSiteInput

/-!
# Full coefficient-machine inputs of the two primed groups

Resolving the rectangular scratch or header reference at each bit position
reproduces the exact tape in Section 9.2. The equality is for all shared bit
assignments. The raw sort and successor messages are never parsed here.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM RAMLayout RAMSerialization

variable {n r H w : ℕ} {L : Lengths}

/-- Number of trailing zero bits after the program prefix, site address, four header bits and
incident ports in a length-`n` input row. -/
def padding (p : UniversalMachine.Program) (n r H w : ℕ) : ℕ :=
  n - ((UniversalMachine.programPrefix p).length + (r + 4 + width r H w))

/-- Positions in a complete primed input row, including the actual program prefix and the
trailing padding for length `n`. -/
abbrev RowField (p : UniversalMachine.Program) (n r H w : ℕ) :=
  Field (UniversalMachine.programPrefix p).length r H w (padding p n r H w)

/-- Identify the typed fields of a fitting primed input row with their bit positions in the
length-`n` tape. -/
def rowIndex (p : UniversalMachine.Program) (hf : ProcessorInput.Fits p n r H w) :
    RowField p n r H w ≃ Fin n :=
  (fieldIndex ..).trans (finCongr (by unfold padding ProcessorInput.Fits at *; omega))

/-- The untested incident bits of a primed group are precisely its assigned
sending bits, copied to their matching ports and clamped at missing ports. -/
def incident (bits : Internal L r H w → Bool) (u : Site r) (j : Fin (width r H w)) : Bool :=
  (assignmentEquiv r H w (fun t ↦ bits (.inr (u.1,t)))).val (u.2, (offset r H w).symm j)

/-- The four one-bit header fields as they appear on a primed tape. -/
def siteHeader (hdr : Header L → Bool) (bits : Internal L r H w → Bool) (u : Site r) :
    ProcessorInput.Header := fun j ↦ (headerRef L u.1 u.2 j).value hdr bits

/-- Full `n`-bit input whose ordered parses occur in (9.4). -/
def input (p : UniversalMachine.Program) (hf : ProcessorInput.Fits p n r H w) (hdr : Header L → Bool)
    (bits : Internal L r H w → Bool) (u : Site r) : Fin n → Bool :=
  ProcessorInput.encode p n u.2 (siteHeader hdr bits u) (incident bits u) hf

private theorem port_value {p : UniversalMachine.Program} (prefixBits : Fin (UniversalMachine.programPrefix p).length → Bool)
    (hdr : Header L → Bool) (bits : Internal L r H w → Bool) (u : Site r) (port : Slot r H w) :
    (cellRef (pad := padding p n r H w) L prefixBits
      (u, .inr (.inr (.inr (.inl port))))).value hdr bits = incident bits u (offset r H w port) := by
  simp only [incident, Equiv.symm_apply_apply]
  change _ = ((source (u.2,port)).map _).getD false
  simp only [cellRef]
  split
  · rename_i h
    rw [h]
    rfl
  · rename_i v h
    conv_rhs => rw [h]
    change bits (.inr (u.1,⟨v,source_shared h⟩)) =
      (if hv : IsSend v then bits (.inr (u.1,⟨v,hv⟩)) else false)
    rw [dite_eq_left (source_shared h)]

private theorem payload_at (p : UniversalMachine.Program) (v : Fin (2^r)) (head : ProcessorInput.Header)
    (inc : Fin (width r H w) → Bool) {j : ℕ} (hj : j < r + 4 + width r H w) :
    (ProcessorInput.tape p n v head inc)[(UniversalMachine.programPrefix p).length + j]? =
      (ProcessorInput.payload v head inc)[j]? := by
  rw [ProcessorInput.tape, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa using hj)]

/-- Every position enumerated by the counter agrees with the universal
machine's actual input, including the literal self-delimiting prefix and all
trailing padding. -/
theorem input_at (p : UniversalMachine.Program) (hf : ProcessorInput.Fits p n r H w)
    (hdr : Header L → Bool) (bits : Internal L r H w → Bool) (u : Site r) (f : RowField p n r H w) :
    input p hf hdr bits u (rowIndex p hf f) =
      (cellRef L (UniversalMachine.programPrefix p).get (u, f)).value hdr bits := by
  let pref := UniversalMachine.programPrefix p
  let head := siteHeader hdr bits u
  let inc := incident bits u
  let i := rowIndex p hf f
  have he : (ProcessorInput.tape p n u.2 head inc)[i.val]? = some (input p hf hdr bits u i) := by
    rw [List.getElem?_eq_getElem (by rw [ProcessorInput.length_tape p _ head inc hf]; exact i.isLt)]
    rfl
  apply Option.some.inj
  rw [← he]
  rcases f with j | (a | (t | (port | pad)))
  · change (ProcessorInput.tape p n u.2 head inc)[j.val]? = some (pref.get j)
    rw [ProcessorInput.tape, List.getElem?_append_left j.isLt, List.getElem?_eq_getElem j.isLt]
    rfl
  · change (ProcessorInput.tape p n u.2 head inc)[pref.length + a.val]? = some (wordBits r u.2 a)
    rw [payload_at p u.2 head inc (by have := a.isLt; omega)]
    exact ProcessorInput.payload_address ..
  · change (ProcessorInput.tape p n u.2 head inc)[pref.length + (r + t.val)]? = some (head t)
    rw [payload_at p u.2 head inc (by have := t.isLt; omega)]
    exact ProcessorInput.payload_header ..
  · change (ProcessorInput.tape p n u.2 head inc)[pref.length + (r + (4 + (offset r H w port).val))]? =
      some ((cellRef L pref.get (u, .inr (.inr (.inr (.inl port))))).value hdr bits)
    rw [port_value (n := n), payload_at p u.2 head inc (by have := (offset r H w port).isLt; omega),
      ← Nat.add_assoc]
    exact ProcessorInput.payload_incident ..
  · change (ProcessorInput.tape p n u.2 head inc)[pref.length + (r + (4 + (width r H w + pad.val)))]? =
      some false
    rw [ProcessorInput.tape, List.getElem?_append_right (by change pref.length ≤ _; omega),
      Nat.add_sub_cancel_left, List.getElem?_append_right (by rw [ProcessorInput.length_payload]; omega),
      ProcessorInput.length_payload]
    have hp := pad.isLt
    change pad.val < padding p n r H w at hp
    have heq : r + (4 + (width r H w + pad.val)) - (r+4+width r H w) = pad.val := by omega
    rw [heq, List.getElem?_eq_getElem (by simpa [padding] using hp)]
    simp

end PrimedInputRAM

end VPVNP
end Computability
end OAI

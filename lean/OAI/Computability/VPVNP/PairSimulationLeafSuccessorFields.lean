import OAI.Computability.VPVNP.PairSimulationLeafSuccessorSelect
import OAI.Computability.VPVNP.PairSimulationLeafSuccessorEndpoints
import OAI.Computability.VPVNP.PairSimulationLeafSortFields

/-!
# Executing both successor fields in the native leaf loader

The machine copies the outgoing bits first, then the incoming bits, using a
descending destination cursor. Nonwrapping edges select their own low-bit
mask class. A missing edge contributes a whole zero field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSuccessorFields

open BurstRAM PrivateRAM CursorNetwork CursorRouting PrimedCounter.GuessWord
open LeafFieldCopy (word)
open LeafIncidentLoad (Stored)

variable {W D H w p r k : ℕ} {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 20 ↪ Fin r} {done : Fin p}

/-- Instruction count for selecting one incoming or outgoing successor field, including
endpoint tests and any class calculation. -/
def selectionTicks (recv : Bool) (v : Fin (2^D)) : ℕ :=
  (if recv then 2 else 3) + (selected recv v).elim 0 (fun j => 5+3*j.val+(if recv then 1 else 0))

theorem selectionTicks_le (recv : Bool) (v : Fin (2^D)) : selectionTicks recv v ≤ 3*D+9 := by
  unfold selectionTicks
  cases h : selected recv v with
  | none => cases recv <;> simp
  | some j => have := j.isLt; cases recv <;> simp <;> omega

private theorem selection_run (link : Linked M pc reg done) (recv : Bool) (base : LocalPort → ℕ)
    (v : Fin (2^D)) (c : Config W p r) (hc : c.pc = pc (if recv then .recvTest else .sendNext))
    (hf : Fixed reg base v w c) (hDW : D < W) :
    ∃ out, Prefix M c (List.replicate (selectionTicks recv v) .tick) out ∧
      out.pc = pc (.prepare recv ((selected recv v).map (useSide recv)) 0) ∧
      out.reg (reg 6) = word W (sourceOffset recv v w) ∧ out.reg (reg 2) = c.reg (reg 2) ∧
      Frame reg c out ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  obtain ⟨d, pre, hd, hcur, hframe, hmem, hp⟩ := endpoint_run link recv base v w c hc hf hDW
  cases hact : active recv v with
  | false =>
    simp only [hact, Bool.false_eq_true, ↓reduceIte] at hd
    simpa [selectionTicks, selected, sourceOffset, hact] using
      (show ∃ out, Prefix M c (List.replicate (if recv then 2 else 3) .tick) out ∧
          out.pc = pc (.prepare recv none 0) ∧ out.reg (reg 6) = 0 ∧ out.reg (reg 2) = c.reg (reg 2) ∧
          Frame reg c out ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent from
        ⟨d, pre, hd.1, hd.2, hcur, hframe, hmem, hp⟩)
  | true =>
    simp only [hact, ite_true] at hd
    obtain ⟨out, tail, hpc, hoff, hc', hf', hm', hp'⟩ := classify_run link recv base v d hd.1
      (hf.of_frame hframe) hDW hact hd.2
    refine ⟨out, ?_, ?_, ?_, hc'.trans hcur, hframe.trans hf', hm'.trans hmem, hp'.trans hp⟩
    · simpa [selectionTicks, selected, hact, ← List.replicate_add] using pre.append tail
    · simpa [selected, hact] using hpc
    · simpa [sourceOffset, selected, hact] using hoff

variable [NeZero D]

/-- The field copy reaches its exit with the private cursor at the lower address and the
selected bits placed there, preserving persistent state and registers outside the writable
slots. -/
structure Result (reg : Fin 20 ↪ Fin r) (exit : Fin p) (lo : ℕ) (bits : List Bool)
    (c out : Config W p r) : Prop where
  pc : out.pc = exit
  cursor : out.reg (reg 2) = word W lo
  frame : Frame reg c out
  memory : out.privateMem = LeafFieldCopy.place lo bits c.privateMem
  persistent : out.persistent = c.persistent

/-- Select and move one entire successor field, restoring every architectural
input needed for the following direction. -/
theorem field_run (link : Linked M pc reg done) (recv : Bool) (base : LocalPort → ℕ)
    (buf : Buffers D H w) (v : Fin (2^D)) (lo : ℕ) (c : Config W p r)
    (hc : c.pc = pc (if recv then .recvTest else .sendNext)) (hf : Fixed reg base v w c) (hDW : D < W)
    (hd : c.reg (reg 2) = word W (lo+8*w)) (stored : Stored base buf c.privateMem)
    (fit : lo+8*w < 2^W) (sourceFit : ∀ a, base a+ramPayloadWidth D H w ≤ 2^W)
    (apart : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+8*w ≤ base a) :
    ∃ out, Prefix M c (List.replicate (selectionTicks recv v+(5*(8*w)+3)) .tick) out ∧
      Result reg (if recv then done else pc .recvTest) lo (succBits recv v buf) c out := by
  obtain ⟨d, prefixRun, he, ho, hcur, fr, mem, persist⟩ := selection_run link recv base v c hc hf hDW
  let use := (selected recv v).map (useSide recv)
  let exit := if recv then done else pc .recvTest
  have fd := hf.of_frame fr
  obtain ⟨out, copy, res⟩ := LeafIncidentLoad.copy_run M (port recv use)
    (pc ∘ Stage.prepare recv use) (pc ∘ Stage.move recv use) (subRegs reg) exit
    (fun j => link (.prepare recv use j)) (fun j => link (.move recv use j))
    base buf (sourceOffset recv v w) (8*w) lo (offsetFits recv v) fit apart sourceFit
    d he fd.bases fd.len ho (hcur.trans hd) fd.one (mem ▸ stored)
  refine ⟨out, ?_, res.pc, res.cursor, fr.trans ?_, ?_, res.persistent.trans persist⟩
  · simpa only [← List.replicate_add] using prefixRun.append copy
  · intro i hi
    exact res.frame i (hi 0 (by decide)) (hi 1 (by decide)) (hi 2 (by decide)) (hi 4 (by decide))
  · simpa only [mem, succBits, use] using res.mem

/-- Total instructions for selecting and copying the outgoing and incoming successor fields,
each of length eight times the word width. -/
def ticks (v : Fin (2^D)) (w : ℕ) :=
  (selectionTicks false v+(5*(8*w)+3)) + (selectionTicks true v+(5*(8*w)+3))

omit [NeZero D] in
theorem ticks_le (v : Fin (2^D)) (w : ℕ) : ticks v w ≤ 80*w+6*D+24 := by
  have := selectionTicks_le false v
  have := selectionTicks_le true v
  dsimp [ticks]
  omega

/-- The complete pair of physical fields is placed at the destination in
the send-then-receive logical order, including both nonwrapping endpoints. -/
theorem pair_run (link : Linked M pc reg done) (base : LocalPort → ℕ)
    (buf : Buffers D H w) (v : Fin (2^D)) (lo : ℕ) (c : Config W p r)
    (hc : c.pc = pc .sendNext) (hf : Fixed reg base v w c) (hDW : D < W)
    (hd : c.reg (reg 2) = word W (lo+16*w)) (stored : Stored base buf c.privateMem)
    (fit : lo+16*w < 2^W) (sourceFit : ∀ a, base a+ramPayloadWidth D H w ≤ 2^W)
    (apart : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+16*w ≤ base a) :
    ∃ out, Prefix M c (List.replicate (ticks v w) .tick) out ∧
      Result reg done lo (succBits false v buf ++ succBits true v buf) c out := by
  have hd' : c.reg (reg 2) = word W ((lo+8*w)+8*w) := by convert hd using 2; omega
  have sep (a : LocalPort) : base a+ramPayloadWidth D H w ≤ lo+8*w ∨ (lo+8*w)+8*w ≤ base a := by
    have := apart a; omega
  obtain ⟨d, send, sr⟩ := field_run link false base buf v (lo+8*w) c hc hf hDW hd' stored
    (by omega) sourceFit sep
  have intact : Stored base buf d.privateMem := by
    rw [sr.memory]
    exact LeafSortFields.stored_place base buf _ _ _ stored (by simp; omega) sourceFit
      (fun a => by simpa only [length_succBits] using sep a)
  obtain ⟨out, receive, rr⟩ := field_run link true base buf v lo d sr.pc (hf.of_frame sr.frame) hDW
    sr.cursor intact (by omega) sourceFit (fun a => by have := apart a; omega)
  refine ⟨out, ?_, rr.pc, rr.cursor, sr.frame.trans rr.frame, ?_, rr.persistent.trans sr.persistent⟩
  · simpa only [ticks, ← List.replicate_add] using send.append receive
  · rw [rr.memory, sr.memory, LeafIncidentLoad.place_append, length_succBits]

end PairSimulation.LeafSuccessorFields

end VPVNP
end Computability
end OAI

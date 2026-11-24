import OAI.Computability.VPVNP.MotifEntry
import OAI.Computability.VPVNP.PrimedCounterGuessWord
import OAI.Computability.VPVNP.PrimedInputRAMHeaders

/-!
# Reading a padded motif field in private RAM

Incident bit strings occupy consecutive private cells. The reader scans a
little-endian field from its high end, doubling its accumulator before adding
the next bit. A private comparison selects a load inside the string and a
literal zero beyond it. Both paths take six instructions per bit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.FieldRead

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord MotifEntry PrimedInputRAM
open scoped Fin.CommRing

variable {w p r k len : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)

private theorem val_word {n : ℕ} (hn : n < 2 ^ w) : (word w n).val = n :=
  Nat.mod_eq_of_lt hn

/-- Registers hold the accumulator, descending cursor, field start, data
end, one, and a temporary bit. All three addresses are absolute. -/
def instruction (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) : Fin 7 → Instr w p r k :=
  ![.jumpEq (reg 1) (reg 2) done (pc 1), .binary .sub (reg 1) (reg 1) (reg 4) (pc 2),
    .binary .add (reg 0) (reg 0) (reg 0) (pc 3), .jumpLt (reg 1) (reg 3) (pc 4) (pc 5),
    .loadPrivate (reg 5) (reg 1) (pc 6), .constant (reg 5) 0 (pc 6),
    .binary .add (reg 0) (reg 0) (reg 5) (pc 0)]

theorem resize_instruction (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) (i : Fin 7) :
    (instruction (w := 1) (k := k) pc reg done i).resize w = instruction pc reg done i := by
  fin_cases i <;> rfl

/-- Require the seven padded-field reader instructions at the assigned labels and registers.
The descending scan doubles the accumulator and adds either the private bit or a padding
zero before returning to its loop test. -/
def Linked (M : Machine w p r k) (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction pc reg done i

/-- A concrete register file and instruction table. Its eighth instruction
returns the result word in register zero. -/
def template : Template 8 6 0 where
  literalWidth := 1
  entry := 0
  code := Fin.lastCases (.returnState 0)
    (instruction Fin.castSucc (Function.Embedding.refl _) (Fin.last 7))

theorem template_linked (pub : Fin 0 → Word w) :
    Linked (template.instantiate w pub) Fin.castSucc (Function.Embedding.refl _) (Fin.last 7) := by
  intro i
  change ((Fin.lastCases _ _ i.castSucc : Instr 1 8 6 0).resize w) = _
  rw [Fin.lastCases_castSucc]
  exact resize_instruction _ _ _ i

variable {M : Machine w p r k} {pc : Fin 7 → Fin p} {reg : Fin 6 ↪ Fin r} {done : Fin p}

private theorem step_at (hl : Linked M pc reg done) (i : Fin 7) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg done i).run M.publicData c := by
  simp [Machine.program, hc, hl i]

/-- Reading the highest bit last in the sum gives the descending Horner recursion. -/
theorem readField_succ_last (bits : Fin len → Bool) (off n : ℕ) :
    readField bits off (n + 1) =
      readField bits off n + (paddedBit bits (off + n)).toNat * 2 ^ n := by
  rw [readField_eq_sum, readField_eq_sum, Fin.sum_univ_castSucc]
  rfl

private theorem body (hl : Linked M pc reg done) (bits : Fin len → Bool) (base pos : ℕ)
    (c : Config w p r) (hc : c.pc = pc 0) (hne : c.reg (reg 1) ≠ c.reg (reg 2))
    (hcursor : c.reg (reg 1) = word w (base + pos + 1)) (hone : c.reg (reg 4) = 1)
    (hend : c.reg (reg 3) = word w (base + len)) (hfit : base + pos < 2 ^ w)
    (hdataFit : base + len < 2 ^ w)
    (hdata : ∀ j : Fin len, c.privateMem (word w (base + j.val)) = encodeBit w (bits j)) :
    ∃ out, Prefix M c (List.replicate 6 .tick) out ∧ out.pc = pc 0 ∧
      out.reg (reg 0) = c.reg (reg 0) + c.reg (reg 0) + word w (paddedBit bits pos).toNat ∧
      out.reg (reg 1) = word w (base + pos) ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 5 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let c₁ := {c with pc := pc 1}
  let c₂ := c₁.put (pc 2) (reg 1) (word w (base + pos))
  let twice := c.reg (reg 0) + c.reg (reg 0)
  let c₃ := c₂.put (pc 3) (reg 0) twice
  let c₄ := {c₃ with pc := if pos < len then pc 4 else pc 5}
  let bit := word w (paddedBit bits pos).toNat
  let c₅ := c₄.put (pc 6) (reg 5) bit
  let out := c₅.put (pc 0) (reg 0) (twice + bit)
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at hl 0 hc]
    simp [instruction, Instr.run, hne, c₁]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at hl 1 rfl]
    change CallAction.localStep (c₁.put (pc 2) (reg 1) (c.reg (reg 1) - c.reg (reg 4))) = _
    simp [c₂, hcursor, hone, word]
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step_at hl 2 rfl]
    change CallAction.localStep (c₂.put (pc 3) (reg 0) (c₂.reg (reg 0) + c₂.reg (reg 0))) = _
    simp [c₃, c₂, c₁, Config.put, twice]
  have hcurs : c₃.reg (reg 1) = word w (base + pos) := by simp [c₃, c₂, Config.put]
  have hlim : c₃.reg (reg 3) = word w (base + len) := by simp [c₃, c₂, c₁, Config.put, hend]
  have hlt : c₃.reg (reg 1) < c₃.reg (reg 3) ↔ pos < len := by
    rw [hcurs, hlim, Fin.lt_def, val_word hfit, val_word hdataFit, Nat.add_lt_add_iff_left]
  have s₃ : M.program.step c₃ = .localStep c₄ := by
    rw [step_at hl 3 rfl]
    change CallAction.localStep
      {c₃ with pc := if c₃.reg (reg 1) < c₃.reg (reg 3) then pc 4 else pc 5} = _
    simp [c₄, hlt]
  have s₄ : M.program.step c₄ = .localStep c₅ := by
    by_cases h : pos < len
    · rw [step_at hl 4 (by simp [c₄, h])]
      change CallAction.localStep (c₄.put (pc 6) (reg 5) (c.privateMem (c₃.reg (reg 1)))) = _
      rw [hcurs, hdata ⟨pos, h⟩]
      cases hb : bits ⟨pos, h⟩ <;> simp [c₅, bit, paddedBit, h, hb, encodeBit]
    · rw [step_at hl 5 (by simp [c₄, h])]
      change CallAction.localStep (c₄.put (pc 6) (reg 5) 0) = _
      simp [c₅, bit, paddedBit, h]
  have s₅ : M.program.step c₅ = .localStep out := by
    rw [step_at hl 6 rfl]
    change CallAction.localStep (c₅.put (pc 0) (reg 0) (c₅.reg (reg 0) + c₅.reg (reg 5))) = _
    simp [out, c₅, c₄, c₃, Config.put]
  refine ⟨out, .tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.tick s₄ (.tick s₅ (.nil _)))))),
    rfl, by simp [out, twice, bit], by simp [out, c₅, c₄, c₃, c₂, Config.put], ?_, rfl, rfl⟩
  intro j h₀ h₁ h₅
  simp [out, c₅, c₄, c₃, c₂, c₁, Config.put, Function.update_of_ne, h₀, h₁, h₅]

/-- Exact private execution with any initial accumulator. All registers
outside the accumulator, cursor and temporary, and all memory cells, are
preserved for the continuation. -/
theorem accumulate (hl : Linked M pc reg done) (bits : Fin len → Bool) (base off n : ℕ)
    (c : Config w p r) (hc : c.pc = pc 0) (hfit : base + off + n < 2 ^ w)
    (hdataFit : base + len < 2 ^ w)
    (hcursor : c.reg (reg 1) = word w (base + off + n))
    (hstop : c.reg (reg 2) = word w (base + off))
    (hend : c.reg (reg 3) = word w (base + len)) (hone : c.reg (reg 4) = 1)
    (hdata : ∀ j : Fin len, c.privateMem (word w (base + j.val)) = encodeBit w (bits j)) :
    ∃ out, Prefix M c (List.replicate (6 * n + 1) .tick) out ∧ out.pc = done ∧
      out.reg (reg 0) = c.reg (reg 0) * word w (2 ^ n) + word w (readField bits off n) ∧
      out.reg (reg 1) = word w (base + off) ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 5 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction n generalizing c with
  | zero =>
    have eq : c.reg (reg 1) = c.reg (reg 2) := hcursor.trans hstop.symm
    have hs : M.program.step c = .localStep {c with pc := done} := by
      rw [step_at hl 0 hc]
      simp [instruction, Instr.run, eq]
    exact ⟨_, .tick hs (.nil _), rfl, by simp [word, readField], hcursor,
      fun _ _ _ _ ↦ rfl, rfl, rfl⟩
  | succ n ih =>
    have ne : c.reg (reg 1) ≠ c.reg (reg 2) := by
      rw [hcursor, hstop]
      intro eq
      have h := congrArg Fin.val eq
      rw [val_word hfit, val_word (by omega : base + off < 2 ^ w)] at h
      omega
    obtain ⟨mid, pre, hm, hacc, hcur, other, hmem, hper⟩ := body hl bits base (off + n) c hc ne
      (by simpa [Nat.add_assoc] using hcursor) hone hend (by omega) hdataFit hdata
    obtain ⟨out, tail, ho, ha, hcur', other', hmem', hper'⟩ := ih mid hm (by omega)
      (by simpa [Nat.add_assoc] using hcur) (by rw [other, hstop] <;> simp)
      (by rw [other, hend] <;> simp) (by rw [other, hone] <;> simp) (hmem ▸ hdata)
    refine ⟨out, ?_, ho, ?_, hcur', fun j h₀ h₁ h₅ ↦
      (other' j h₀ h₁ h₅).trans (other j h₀ h₁ h₅), hmem'.trans hmem, hper'.trans hper⟩
    · convert pre.append tail using 1
      rw [← List.replicate_add]
      congr 1
      omega
    · rw [ha, hacc, readField_succ_last]
      simp only [word, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- A zeroed accumulator and a field at most one word wide recover the
natural value. The prefix length agrees exactly with the abstract meter,
also for the empty field and for fields extending into padding. -/
theorem native_read (hl : Linked M pc reg done) (bits : Fin len → Bool) (base off n : ℕ)
    (c : Config w p r) (hc : c.pc = pc 0) (hn : n ≤ w) (hfit : base + off + n < 2 ^ w)
    (hdataFit : base + len < 2 ^ w)
    (hzero : c.reg (reg 0) = 0) (hcursor : c.reg (reg 1) = word w (base + off + n))
    (hstop : c.reg (reg 2) = word w (base + off)) (hend : c.reg (reg 3) = word w (base + len))
    (hone : c.reg (reg 4) = 1)
    (hdata : ∀ j : Fin len, c.privateMem (word w (base + j.val)) = encodeBit w (bits j)) :
    ∃ out, Prefix M c (List.replicate (meteredField bits off n).2 .tick) out ∧ out.pc = done ∧
      (out.reg (reg 0)).val = readField bits off n ∧ out.reg (reg 1) = word w (base + off) ∧
      (∀ j, j ≠ reg 0 → j ≠ reg 1 → j ≠ reg 5 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  rw [meteredField_spec]
  obtain ⟨out, pre, ho, ha, hcur, other, hmem, hper⟩ := accumulate hl bits base off n c hc
    hfit hdataFit hcursor hstop hend hone hdata
  refine ⟨out, pre, ho, ?_, hcur, other, hmem, hper⟩
  rw [ha, hzero, zero_mul, zero_add, val_word]
  exact (readField_lt bits off n).trans_le (Nat.pow_le_pow_right (by decide) hn)

end PairSimulation.FieldRead

end VPVNP
end Computability
end OAI

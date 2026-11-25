import OAI.Computability.VPVNP.PrimedStackRAMCode
import Mathlib.Logic.Embedding.Basic

namespace OAI
/-! # Fetching a six-word instruction from external RAM

The code uses a register for the source program counter, two scratch
registers and six result registers. It works inside any larger register file.
-/

namespace ThreeFlat.RAM.FetchWords

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.PrimedStackRAM

variable {r k p w : ℕ}

/-- Layout of the six result words in the nine-register block. -/
def slot (i : Fin 6) : Fin 9 := ⟨i.val + 3, by omega⟩

private def header (ρ : Fin 9 ↪ Fin r) : List (Op r k) :=
  [.constant (ρ 1) 3, .binary .mul (ρ 1) (ρ 0) (ρ 1),
   .binary .add (ρ 1) (ρ 1) (ρ 1), .constant (ρ 2) 1]

private def fetch (ρ : Fin 9 ↪ Fin r) (i : Fin 6) : List (Op r k) :=
  [.binary .add (ρ 1) (ρ 1) (ρ 2), .read (ρ (slot i)) (ρ 1)]

private def prefixOps (ρ : Fin 9 ↪ Fin r) : ℕ → List (Op r k)
  | 0 => header ρ
  | n + 1 => prefixOps ρ n ++ fetch ρ (Fin.ofNat 6 n)

/-- Compute six times the supplied counter. Each read increments the
address first, thereby skipping the one-word program header. -/
def block (ρ : Fin 9 ↪ Fin r) : List (Op r k) := prefixOps ρ 6

@[simp] theorem block_length (ρ : Fin 9 ↪ Fin r) : (block (k := k) ρ).length = 16 := rfl

/-- Instruction fetch, operand access, arithmetic, and destination writes together
have total work 78 in the source machine's word-work accounting. -/
theorem block_wordWork (ρ : Fin 9 ↪ Fin r) (next bad : Fin p) (width : ℕ) :
    ((block (k := k) ρ).map fun op => ((op.emit next bad).resize width).wordWork).sum = 78 := by
  simp [block, prefixOps, header, fetch, Op.emit, Instr.resize, Instr.wordWork]

private def addr (pc : Word w) : ℕ → Word w
  | 0 => (pc * Fin.ofNat _ 3) + (pc * Fin.ofNat _ 3)
  | j + 1 => addr pc j + Fin.ofNat _ 1

private theorem addr_val (pc : Word w) (i : ℕ) (fit : 6 * pc.val + i < 2 ^ w)
    (wide : 3 < 2 ^ w) : (addr pc i).val = 6 * pc.val + i := by
  induction i with
  | zero =>
    have h3 : pc.val * 3 < 2 ^ w := by omega
    have h6 : pc.val * 3 + pc.val * 3 < 2 ^ w := by omega
    simp [addr, Fin.val_add, Fin.val_mul, Fin.ofNat, Nat.mod_eq_of_lt wide,
      Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h6]
    omega
  | succ i ih =>
    have h := ih (by omega)
    have hone : 1 < 2 ^ w := by omega
    simp [addr, Fin.val_add, Fin.ofNat, h, Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt fit,
      Nat.add_assoc]

private theorem slot_ne_one (i : Fin 6) : slot i ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  change i.val + 3 = 1 at h'
  omega

private theorem slot_ne_two (i : Fin 6) : slot i ≠ 2 := by
  intro h
  have h' := congrArg Fin.val h
  change i.val + 3 = 2 at h'
  omega

private theorem slot_inj : Function.Injective slot := by
  intro i j h
  have e := congrArg Fin.val h
  exact Fin.ext (Nat.add_right_cancel e)

private theorem trace_fetch (ρ : Fin 9 ↪ Fin r) (pub : Fin k → Word w) (state : Word w)
    (rs : Regs w r) (mem : Memory w) (j : Fin 6) :
    let a := rs (ρ 1) + rs (ρ 2)
    trace pub state (fetch ρ j) rs mem =
      some ([.tick, .read a (mem a.val)],
        Function.update (Function.update rs (ρ 1) a) (ρ (slot j)) (mem a.val), mem) := by
  simp [fetch, trace, Op.effect, BinaryOp.eval]

private theorem trace_prefix (ρ : Fin 9 ↪ Fin r) (pub : Fin k → Word w) (state : Word w)
    (regs : Regs w r) (mem : Memory w) :
    ∀ n ≤ 6, ∃ (es : List (Event w)) (out : Regs w r),
      trace pub state (prefixOps ρ n) regs mem = some (es, out, mem) ∧
      es.length = 4 + 2 * n ∧ out (ρ 1) = addr (regs (ρ 0)) n ∧
      out (ρ 2) = Fin.ofNat _ 1 ∧ ∀ i : Fin 6, i.val < n →
        out (ρ (slot i)) = mem (addr (regs (ρ 0)) (i.val + 1)).val := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    · simp [addr, BinaryOp.eval]
    · simp
    · intro i hi; omega
  | succ n ih =>
    intro hn
    obtain ⟨es, out, run, len, address, one, earlier⟩ := ih (by omega)
    let j : Fin 6 := Fin.ofNat 6 n
    have hj : j.val = n := Nat.mod_eq_of_lt (by omega)
    let a := addr (regs (ρ 0)) (n + 1)
    have ha : out (ρ 1) + out (ρ 2) = a := by rw [address, one]; rfl
    let out' := Function.update (Function.update out (ρ 1) a) (ρ (slot j)) (mem a.val)
    refine ⟨es ++ [.tick, .read a (mem a.val)], out', ?_, ?_, ?_, ?_, ?_⟩
    · rw [prefixOps, trace_append, run]
      simp [trace_fetch, j, ha, out']
    · simp [len]; omega
    · simp [out', Ne.symm (slot_ne_one j), a]
    · simp [out', Ne.symm (slot_ne_two j), one]
    · intro i hi
      by_cases e : i = j
      · subst i; simp [out', hj, a]
      · have ne := slot_inj.ne e
        have hlt : i.val < n := by
          have hv : i.val ≠ j.val := by intro h; exact e (Fin.ext h)
          omega
        simp [out', ne, slot_ne_one, earlier i hlt]

/-- The evaluator reads consecutive words from the program text and leaves
external memory intact. The caller supplies the program counter in register zero. -/
theorem trace_block (ρ : Fin 9 ↪ Fin r) (pub : Fin k → Word w) (state : Word w)
    (regs : Regs w r) (mem : Memory w) (fit : 6 * (regs (ρ 0)).val + 6 < 2 ^ w) :
    ∃ (es : List (Event w)) (out : Regs w r),
      trace pub state (block ρ) regs mem = some (es, out, mem) ∧ es.length = 16 ∧
        ∀ i : Fin 6, out (ρ (slot i)) = mem (1 + 6 * (regs (ρ 0)).val + i.val) := by
  obtain ⟨es, out, run, len, _, _, h⟩ := trace_prefix ρ pub state regs mem 6 (by decide)
  refine ⟨es, out, run, len, ?_⟩
  intro i
  rw [h i i.isLt, addr_val _ _ (by have := i.isLt; omega) (by omega)]
  congr 1
  omega

/-- Execute the compiled block from any occurrence in a native finite machine,
then use the six result registers in the continuation. -/
theorem execute (ρ : Fin 9 ↪ Fin r) {M : Machine w p r k} {bad start stop : Fin p}
    (linked : Contains M bad start (block ρ) stop) (rejects : M.code bad = .reject)
    (state : Word w) (regs : Regs w r) (priv : Word w → Word w) (mem : Memory w)
    (bits : List Bool) (fuel : ℕ) (fit : 6 * (regs (ρ 0)).val + 6 < 2 ^ w) :
    ∃ (es : List (Event w)) (out : Regs w r), es.length = 16 ∧
      (∀ i : Fin 6, out (ρ (slot i)) = mem (1 + 6 * (regs (ρ 0)).val + i.val)) ∧
      Computability.VPVNP.BurstRAM.execute M.program (fuel + 16) ⟨start, state, regs, priv⟩ mem bits =
        (Computability.VPVNP.BurstRAM.execute M.program fuel ⟨stop, state, out, priv⟩ mem bits).map
          (fun t => ⟨es ++ t.events, t.result⟩) := by
  obtain ⟨es, out, htrace, hl, hout⟩ := trace_block ρ M.publicData state regs mem fit
  refine ⟨es, out, hl, hout, ?_⟩
  rw [← block_length (k := k) ρ, linked.execute rejects, run_eq_trace, htrace]
  rfl

/-- The straight-line compiler produces a native table which can return any
designated field of the fetched row in seventeen instructions including the return. -/
theorem execute_template_word (ρ : Fin 9 ↪ Fin r) (i : Fin 6) (pub : Fin k → Word w)
    (state : Word w) (regs : Regs w r) (priv : Word w → Word w) (mem : Memory w)
    (fit : 6 * (regs (ρ 0)).val + 6 < 2 ^ w) :
    let M := (template (block ρ) (ρ (slot i))).instantiate w pub
    ∃ es : List (Event w), es.length = 16 ∧
      Computability.VPVNP.BurstRAM.execute M.program 17 ⟨M.entry, state, regs, priv⟩ mem [] =
        some ⟨es, some (mem (1 + 6 * (regs (ρ 0)).val + i.val))⟩ := by
  dsimp only
  obtain ⟨es, out, htrace, hl, hout⟩ := trace_block ρ pub state regs mem fit
  refine ⟨es, hl, ?_⟩
  rw [show 17 = 1 + (block (k := k) ρ).length from rfl, execute_template, run_eq_trace, htrace]
  simp [hout]

end ThreeFlat.RAM.FetchWords

end OAI

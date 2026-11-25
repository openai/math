import OAI.ThreeFlat.RAM.ProgramEncoding
import OAI.Computability.VPVNP.RAMSerialization
import OAI.Computability.VPVNP.RAMUniform

namespace OAI
/-! # Supplying the interpreter's text in the bit advice

The executable decoder reads words from the bit segment used as data by the
diagonal program. Extra advice bits beyond the text may contain the remaining
public parameters or evaluator advice. -/

namespace ThreeFlat.RAM

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMSerialization

variable {w p r k : ℕ}

/-- Serialize the complete finite instruction and public-data tables. -/
def programBits (M : Machine w p r k) : Fin ((1 + 6*p + k) * w) → Bool :=
  arrayBits _ _ (fun i => programWords M i.val)

/-- Read a program-sized prefix, decoding each little-endian word independently. -/
def adviceWords (w words : ℕ) (bits : Fin (words*w) → Bool) : Memory w :=
  fun i => if h : i < words then (arrayBits words w).symm bits ⟨i,h⟩ else 0

@[simp] theorem adviceWords_programBits (M : Machine w p r k) :
    adviceWords w (1 + 6*p + k) (programBits M) = programWords M := by
  funext i
  by_cases h : i < 1 + 6*p + k
  · simp [adviceWords, programBits, h]
  · simp [adviceWords, h, programWords_outside M (Nat.le_of_not_gt h)]

/-- From a larger advice string, use only the prefix occupied by the text. -/
def readAdvicePrefix (w p r k : ℕ) {q : ℕ} (fits : (1 + 6*p + k)*w ≤ q)
    (D : Fin q → Bool) : Option (Machine w p r k) :=
  readProgram w p r k (adviceWords w _ (fun i => D (Fin.castLE fits i)))

/-- Reading a text prefix is independent of the rest of the advice. -/
theorem readAdvicePrefix_eq (M : Machine w p r k) (h : TextFits w p r k)
    {q : ℕ} (fits : (1 + 6*p + k)*w ≤ q) (D : Fin q → Bool)
    (prefix_eq : ∀ i, D (Fin.castLE fits i) = programBits M i) :
    readAdvicePrefix w p r k fits D = some M := by
  simp [readAdvicePrefix, funext prefix_eq, readProgram_programWords M h]

/-- Write an executable program at the start of the advice, preserving every
bit after the prefix. -/
def installProgram (M : Machine w p r k) {q : ℕ} (tail : Fin q → Bool) (i : Fin q) : Bool :=
  if hi : i.val < (1 + 6*p + k)*w then programBits M ⟨i.val,hi⟩ else tail i

theorem readAdvicePrefix_install (M : Machine w p r k) (h : TextFits w p r k)
    {q : ℕ} (fits : (1 + 6*p + k)*w ≤ q) (tail : Fin q → Bool) :
    readAdvicePrefix w p r k fits (installProgram M tail) = some M :=
  readAdvicePrefix_eq M h fits _ fun i => by simp [installProgram, i.isLt]

theorem installProgram_after (M : Machine w p r k) {q : ℕ} (tail : Fin q → Bool) (i : Fin q)
    (hi : (1 + 6*p + k)*w ≤ i.val) : installProgram M tail i = tail i := by
  simp [installProgram, Nat.not_lt_of_ge hi]

/-- Put one advice bit in each address of a dedicated input-memory segment. -/
def memoryWithAdvice (base : ℕ) {q : ℕ} (D : Fin q → Bool) (input : Memory w) : Memory w :=
  fun a => if h : base ≤ a ∧ a-base < q then
    if D ⟨a-base, h.2⟩ then 1 else 0
  else input a

theorem memoryWithAdvice_at (base : ℕ) {q : ℕ} (D : Fin q → Bool) (input : Memory w) (i : Fin q) :
    memoryWithAdvice base D input (base + i.val) = if D i then 1 else 0 := by
  simp [memoryWithAdvice, i.isLt]

theorem memoryWithAdvice_outside (base : ℕ) {q : ℕ} (D : Fin q → Bool) (input : Memory w)
    {a : ℕ} (outside : a < base ∨ base+q ≤ a) : memoryWithAdvice base D input a = input a := by
  have h : ¬ (base ≤ a ∧ a-base < q) := by omega
  simp [memoryWithAdvice, h]

/-- The same advice supplies the instruction text and is available to external
reads during the run. No literal copy of the program is needed in the text. -/
theorem execute_installed (M : Machine w p r k) (h : TextFits w p r k)
    {q : ℕ} (fits : (1 + 6*p + k)*w ≤ q) (tail : Fin q → Bool)
    (fuel : ℕ) (c : Config w p r) (base : ℕ) (input : Memory w) (bits : List Bool) :
    let D := installProgram M tail
    let m := memoryWithAdvice base D input
    (readAdvicePrefix w p r k fits D).bind (fun P => execute P.program fuel c m bits) =
      execute M.program fuel c m bits := by
  dsimp only
  rw [readAdvicePrefix_install M h]
  rfl

/-- Increasing the runtime width does not change any field of a fixed
instruction row once the literal size fits. -/
theorem instructionRow_resize {v : ℕ} (i : Instr v p r k) (hw : v ≤ w) :
    instructionRow (i.resize w) = instructionRow i := by
  cases i <;> simp [Instr.resize, instructionRow]
  rename_i dst literal next
  exact Nat.mod_eq_of_lt (literal.isLt.trans_le (Nat.pow_le_pow_right (by decide) hw))

theorem fetchRow_template (T : Template p r k) (pub : Fin k → Word w)
    (h : TextFits w p r k) (hw : T.literalWidth ≤ w) (pc : Fin p) :
    fetchRow (programWords (T.instantiate w pub)) pc.val = instructionRow (T.code pc) := by
  rw [fetchRow_programWords _ h]
  exact instructionRow_resize _ hw

/-- At the paper's word width the program and a further exponential advice
segment both fit into the input of length `2^(u^3)` for large `u`. -/
theorem programBits_add_advice_fit (p k u : ℕ) (hu : 16 * (1 + 6*p + k) ≤ u) :
    (1 + 6*p + k) * (16*u^10) + 2^(u^2) ≤ 2^(u^3) := by
  have hu16 : 16 ≤ u := by omega
  have hp : u ≤ 2^u := Nat.lt_two_pow_self.le
  have h11 : 11*u ≤ u^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right u (by omega)
  have hbits : (1 + 6*p + k) * (16*u^10) ≤ 2^(u^2) := calc
    _ = (16 * (1 + 6*p + k)) * u^10 := by ac_rfl
    _ ≤ 2 ^ u * (2 ^ u)^10 := Nat.mul_le_mul (hu.trans hp) (Nat.pow_le_pow_left hp _)
    _ = 2^(11*u) := by rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
    _ ≤ 2^(u^2) := Nat.pow_le_pow_right (by decide) h11
  have hu2 : 1 ≤ u^2 := Nat.one_le_pow _ _ (by omega)
  have hc : u^2+1 ≤ u^3 := calc
    _ ≤ u^2 + u^2 := by omega
    _ = u^2 * 2 := by omega
    _ ≤ u^2 * u := Nat.mul_le_mul_left _ (by omega)
    _ = _ := (pow_succ ..).symm
  calc
    _ ≤ 2^(u^2) + 2^(u^2) := Nat.add_le_add_right hbits _
    _ = 2^(u^2+1) := by rw [pow_succ]; omega
    _ ≤ 2^(u^3) := Nat.pow_le_pow_right (by decide) hc

end ThreeFlat.RAM

end OAI

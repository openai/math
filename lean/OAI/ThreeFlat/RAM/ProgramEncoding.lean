import OAI.Computability.VPVNP.RAMProgram

namespace OAI
/-! # Word-addressed RAM text

The same array exposes the entry counter, the opcode and operand words, and
the public constants to the simulated program and to its evaluator. Rows have
a fixed stride, including for halting instructions. -/

namespace ThreeFlat.RAM

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

variable {w p r k : ℕ}

/-- One opcode and at most five operands. -/
structure InstructionRow where
  tag : ℕ
  a : ℕ := 0
  b : ℕ := 0
  c : ℕ := 0
  d : ℕ := 0
  e : ℕ := 0

def InstructionRow.get (s : InstructionRow) (j : Fin 6) : ℕ :=
  match j.val with
  | 0 => s.tag
  | 1 => s.a
  | 2 => s.b
  | 3 => s.c
  | 4 => s.d
  | _ => s.e

def opNumber : BinaryOp → ℕ
  | .add => 0
  | .sub => 1
  | .mul => 2
  | .div => 3
  | .mod => 4
  | .bitAnd => 5
  | .bitOr => 6
  | .bitXor => 7
  | .shiftLeft => 8
  | .shiftRight => 9

def readOp : ℕ → Option BinaryOp
  | 0 => some .add
  | 1 => some .sub
  | 2 => some .mul
  | 3 => some .div
  | 4 => some .mod
  | 5 => some .bitAnd
  | 6 => some .bitOr
  | 7 => some .bitXor
  | 8 => some .shiftLeft
  | 9 => some .shiftRight
  | _ => none

@[simp] theorem readOp_number (op : BinaryOp) : readOp (opNumber op) = some op := by
  cases op <;> rfl

def instructionRow : Instr w p r k → InstructionRow
  | .constant j a l => ⟨0,j,a,l,0,0⟩
  | .publicWord j i l => ⟨1,j,i,l,0,0⟩
  | .stateWord j l => ⟨2,j,l,0,0,0⟩
  | .copy j i l => ⟨3,j,i,l,0,0⟩
  | .binary op j a b l => ⟨4,opNumber op,j,a,b,l⟩
  | .loadPrivate j a l => ⟨5,j,a,l,0,0⟩
  | .storePrivate a j l => ⟨6,a,j,l,0,0⟩
  | .jumpEq a b y n => ⟨7,a,b,y,n,0⟩
  | .jumpLt a b y n => ⟨8,a,b,y,n,0⟩
  | .choose y n => ⟨9,y,n,0,0,0⟩
  | .readExternal j a l => ⟨10,j,a,l,0,0⟩
  | .writeExternal a j l => ⟨11,a,j,l,0,0⟩
  | .returnState j => ⟨12,j,0,0,0,0⟩
  | .accept => ⟨13,0,0,0,0,0⟩
  | .reject => ⟨14,0,0,0,0,0⟩

def bounded (n i : ℕ) : Option (Fin n) :=
  if h : i < n then some ⟨i,h⟩ else none

@[simp] theorem bounded_val {n : ℕ} (i : Fin n) : bounded n i.val = some i := by
  simp [bounded]

/-- Reject out-of-range opcodes or operands rather than truncating them. -/
def decodeRow (w p r k : ℕ) (s : InstructionRow) : Option (Instr w p r k) := do
  let reg := bounded r
  let pc := bounded p
  match s.tag with
  | 0 => return .constant (← reg s.a) (← bounded _ s.b) (← pc s.c)
  | 1 => return .publicWord (← reg s.a) (← bounded k s.b) (← pc s.c)
  | 2 => return .stateWord (← reg s.a) (← pc s.b)
  | 3 => return .copy (← reg s.a) (← reg s.b) (← pc s.c)
  | 4 => return .binary (← readOp s.a) (← reg s.b) (← reg s.c) (← reg s.d) (← pc s.e)
  | 5 => return .loadPrivate (← reg s.a) (← reg s.b) (← pc s.c)
  | 6 => return .storePrivate (← reg s.a) (← reg s.b) (← pc s.c)
  | 7 => return .jumpEq (← reg s.a) (← reg s.b) (← pc s.c) (← pc s.d)
  | 8 => return .jumpLt (← reg s.a) (← reg s.b) (← pc s.c) (← pc s.d)
  | 9 => return .choose (← pc s.a) (← pc s.b)
  | 10 => return .readExternal (← reg s.a) (← reg s.b) (← pc s.c)
  | 11 => return .writeExternal (← reg s.a) (← reg s.b) (← pc s.c)
  | 12 => return .returnState (← reg s.a)
  | 13 => return .accept
  | 14 => return .reject
  | _ => none

@[simp] theorem decode_instructionRow (i : Instr w p r k) :
    decodeRow w p r k (instructionRow i) = some i := by
  cases i <;> simp [instructionRow, decodeRow]

/-- The text occupies one entry word, six words per instruction, and then one
word per public operand. Locations past this segment are zero. -/
def programWords (M : Machine w p r k) : Memory w
  | 0 => Fin.ofNat _ M.entry.val
  | i + 1 =>
    if h : i / 6 < p then
      Fin.ofNat _ ((instructionRow (M.code ⟨i/6,h⟩)).get ⟨i%6, Nat.mod_lt _ (by decide)⟩)
    else if h' : i - 6*p < k then M.publicData ⟨i-6*p,h'⟩
    else 0

/-- Every operand and every address in the text can be represented by a word. -/
structure TextFits (w p r k : ℕ) : Prop where
  opcode : 14 < 2 ^ w
  registers : r ≤ 2 ^ w
  addresses : 1 + 6*p + k ≤ 2 ^ w

private theorem row_word_fits (h : TextFits w p r k) (i : Instr w p r k) (j : Fin 6) :
    (instructionRow i).get j < 2^w := by
  have ha := h.addresses
  have hb := h.registers
  have hc := h.opcode
  have ho (op : BinaryOp) : opNumber op < 10 := by cases op <;> decide
  cases i <;> simp only [instructionRow, InstructionRow.get] <;> split
    <;> first | omega | exact Nat.lt_trans (ho _) (by omega)

/-- Address of the opcode word. The following five addresses are its operands. -/
def instructionAddress (pc : ℕ) := 1 + 6*pc

theorem programWords_instruction (M : Machine w p r k) (h : TextFits w p r k)
    (pc : Fin p) (j : Fin 6) :
    (programWords M (instructionAddress pc + j.val)).val = (instructionRow (M.code pc)).get j := by
  have hj := j.isLt
  have hadd : instructionAddress pc + j.val = 6 * pc.val + j.val + 1 := by
    dsimp [instructionAddress]; omega
  have hdiv : (6 * pc.val + j.val) / 6 = pc.val := by omega
  have hmod : (6 * pc.val + j.val) % 6 = j.val := by omega
  simp [hadd, programWords, hdiv, hmod, pc.isLt, Fin.ofNat, Nat.mod_eq_of_lt (row_word_fits h _ _)]

theorem programWords_public (M : Machine w p r k) (j : Fin k) :
    programWords M (1 + 6*p + j.val) = M.publicData j := by
  have hadd : 1 + 6*p + j.val = 6*p + j.val + 1 := by omega
  have hn : ¬(6*p + j.val)/6 < p := by omega
  simp [hadd, programWords, hn, j.isLt]

theorem programWords_outside (M : Machine w p r k) {i : ℕ} (hi : 1 + 6*p + k ≤ i) :
    programWords M i = 0 := by
  cases i with
  | zero => omega
  | succ i =>
    have h : ¬ i/6 < p := by omega
    have h' : ¬ i - 6*p < k := by omega
    simp [programWords, h, h']

/-- Six reads from the program-as-data array, in the order of their addresses. -/
def fetchRow (data : Memory w) (pc : ℕ) : InstructionRow :=
  let atField := fun j : ℕ => (data (instructionAddress pc + j)).val
  ⟨atField 0, atField 1, atField 2, atField 3, atField 4, atField 5⟩

@[simp] theorem fetchRow_programWords (M : Machine w p r k) (h : TextFits w p r k) (pc : Fin p) :
    fetchRow (programWords M) pc.val = instructionRow (M.code pc) := by
  have hr := programWords_instruction M h pc
  rcases eq : instructionRow (M.code pc) with ⟨tag,a,b,c,d,e⟩
  simp only [fetchRow, InstructionRow.mk.injEq]
  exact ⟨by simpa [fetchRow, eq, InstructionRow.get] using hr 0,
    by simpa [fetchRow, eq, InstructionRow.get] using hr 1,
    by simpa [fetchRow, eq, InstructionRow.get] using hr 2,
    by simpa [fetchRow, eq, InstructionRow.get] using hr 3,
    by simpa [fetchRow, eq, InstructionRow.get] using hr 4,
    by simpa [fetchRow, eq, InstructionRow.get] using hr 5⟩

/-- Interpret an advice segment as a program. A malformed entry counter
fails to start, and a malformed instruction decodes to a rejecting halt. -/
def readProgram (w p r k : ℕ) (data : Memory w) : Option (Machine w p r k) := do
  let entry ← bounded p (data 0).val
  return {
    entry
    code := fun i => (decodeRow w p r k (fetchRow data i.val)).getD .reject
    publicData := fun i => data (1 + 6*p + i.val)
  }

@[simp] theorem readProgram_programWords (M : Machine w p r k) (h : TextFits w p r k) :
    readProgram w p r k (programWords M) = some M := by
  have hp : M.entry.val < 2^w := by
    have := h.addresses
    have := M.entry.isLt
    omega
  have he : (programWords M 0).val = M.entry.val := by simp [programWords, Fin.ofNat, Nat.mod_eq_of_lt hp]
  simp [readProgram, he, fetchRow_programWords M h, programWords_public]

/-- The original interpreter and an interpreter fetching its text from advice
give the same path report for every choice string, memory and fuel cap. -/
theorem execute_readProgram (M : Machine w p r k) (h : TextFits w p r k) (fuel : ℕ)
    (c : Config w p r) (mem : Memory w) (choices : List Bool) :
    (readProgram w p r k (programWords M)).bind
      (fun P => execute P.program fuel c mem choices) =
      execute M.program fuel c mem choices := by
  rw [readProgram_programWords M h]
  rfl

end ThreeFlat.RAM

end OAI

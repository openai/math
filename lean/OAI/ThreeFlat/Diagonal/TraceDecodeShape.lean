import OAI.ThreeFlat.RAM.ProgramEncoding

namespace OAI
/-! # Decoding a ROM row against a finite RAM instruction shape

A shape retains all finite operand indices. A constant instruction takes its
literal from the row, and each opcode ignores the fields following its operands.
-/

namespace ThreeFlat.Diagonal.TraceDecodeShape

open RAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

variable {w p r k : ℕ}

/-- Erase the word-width-dependent literal while retaining the finite operand indices. -/
def erase : Instr w p r k → Instr 0 p r k
  | .constant j _ l => .constant j 0 l
  | .publicWord j a l => .publicWord j a l
  | .stateWord j l => .stateWord j l
  | .copy j a l => .copy j a l
  | .binary op j a b l => .binary op j a b l
  | .loadPrivate j a l => .loadPrivate j a l
  | .storePrivate a j l => .storePrivate a j l
  | .jumpEq a b y n => .jumpEq a b y n
  | .jumpLt a b y n => .jumpLt a b y n
  | .choose y n => .choose y n
  | .readExternal j a l => .readExternal j a l
  | .writeExternal a j l => .writeExternal a j l
  | .returnState j => .returnState j
  | .accept => .accept
  | .reject => .reject

/-- Fill the literal slot of a shape. -/
def instantiate (z : Instr 0 p r k) (v : Word w) : Instr w p r k :=
  match z with
  | .constant j _ l => .constant j v l
  | .publicWord j a l => .publicWord j a l
  | .stateWord j l => .stateWord j l
  | .copy j a l => .copy j a l
  | .binary op j a b l => .binary op j a b l
  | .loadPrivate j a l => .loadPrivate j a l
  | .storePrivate a j l => .storePrivate a j l
  | .jumpEq a b y n => .jumpEq a b y n
  | .jumpLt a b y n => .jumpLt a b y n
  | .choose y n => .choose y n
  | .readExternal j a l => .readExternal j a l
  | .writeExternal a j l => .writeExternal a j l
  | .returnState j => .returnState j
  | .accept => .accept
  | .reject => .reject

@[simp] theorem erase_instantiate (z : Instr 0 p r k) (v : Word w) :
    erase (instantiate z v) = z := by
  cases z <;> try rfl
  simp only [instantiate, erase, Instr.constant.injEq, true_and, and_true]
  exact @Subsingleton.elim (Fin 1) inferInstance _ _

/-- The live opcode and operand fields. Width-dependent literals are read directly. -/
def tests : Instr 0 p r k → List (Fin 6 × ℕ)
  | .constant j _ l => [(0, 0), (1, j), (3, l)]
  | .publicWord j a l => [(0, 1), (1, j), (2, a), (3, l)]
  | .stateWord j l => [(0, 2), (1, j), (2, l)]
  | .copy j a l => [(0, 3), (1, j), (2, a), (3, l)]
  | .binary op j a b l => [(0, 4), (1, opNumber op), (2, j), (3, a), (4, b), (5, l)]
  | .loadPrivate j a l => [(0, 5), (1, j), (2, a), (3, l)]
  | .storePrivate a j l => [(0, 6), (1, a), (2, j), (3, l)]
  | .jumpEq a b y n => [(0, 7), (1, a), (2, b), (3, y), (4, n)]
  | .jumpLt a b y n => [(0, 8), (1, a), (2, b), (3, y), (4, n)]
  | .choose y n => [(0, 9), (1, y), (2, n)]
  | .readExternal j a l => [(0, 10), (1, j), (2, a), (3, l)]
  | .writeExternal a j l => [(0, 11), (1, a), (2, j), (3, l)]
  | .returnState j => [(0, 12), (1, j)]
  | .accept  => [(0, 13)]
  | .reject  => [(0, 14)]

theorem tests_length_le (z : Instr 0 p r k) : (tests z).length ≤ 6 := by
  cases z <;> simp [tests]

private theorem opNumber_lt (op : BinaryOp) : opNumber op < 10 := by
  cases op <;> decide

/-- Every tested natural number is represented exactly by a RAM word for a fitting program. -/
theorem test_lt (fits : TextFits w p r k) {z : Instr 0 p r k} {j : Fin 6} {n : ℕ}
    (h : (j,n) ∈ tests z) : n < 2^w := by
  have hp := fits.addresses
  have hr := fits.registers
  have htag := fits.opcode
  have hob (op : BinaryOp) : opNumber op < 2^w :=
    Nat.lt_trans (opNumber_lt op) (show 10 < 2^w by omega)
  suffices hall : ∀ field ∈ tests z, field.2 < 2^w from hall _ h
  cases z <;> simp only [tests, List.forall_mem_cons]
  all_goals repeat' apply And.intro
  all_goals first
    | exact List.forall_mem_nil _
    | exact hob _
    | exact Fin.isLt _ | exact (Fin.isLt _).trans_le hr
    | omega

/-- Every tested field agrees with the corresponding value in the public instruction shape. -/
def «matches» (R : InstructionRow) (z : Instr 0 p r k) : Prop :=
  ∀ field ∈ tests z, R.get field.1 = field.2

private theorem bounded_some_iff {n v : ℕ} {i : Fin n} :
    bounded n v = some i ↔ v = i.val := by
  constructor
  · intro h
    unfold bounded at h
    split at h
    · exact congrArg Fin.val (Option.some.inj h)
    · contradiction
  · rintro rfl
    exact bounded_val i

private theorem readOp_some_iff {v : ℕ} {op : BinaryOp} :
    readOp v = some op ↔ v = opNumber op := by
  constructor
  · intro h
    unfold readOp at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    exact readOp_number op

/-- Every successfully decoded instruction agrees with every live field in its erased shape. -/
theorem matches_erase_of_decode {R : InstructionRow} {i : Instr w p r k}
    (h : decodeRow w p r k R = some i) : «matches» R (erase i) := by
  unfold decodeRow at h
  split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, bounded_some_iff,
    readOp_some_iff, Option.pure_def, Option.some.injEq] at h
  all_goals repeat' obtain ⟨v, hv, h⟩ := h
  all_goals simp_all [«matches», tests, erase, InstructionRow.get]

/-- A ROM word fits the register width, so a matching literal may be used without truncation. -/
theorem decode_of_matches {R : InstructionRow} (hword : R.b < 2^w) (z : Instr 0 p r k)
    (h : «matches» R z) : decodeRow w p r k R = some (instantiate z (Fin.ofNat _ R.b)) := by
  cases z <;> simp [«matches», tests, InstructionRow.get] at h
  all_goals repeat' obtain ⟨h₁, h⟩ := h
  all_goals simp_all [decodeRow, instantiate, bounded, Fin.ofNat, Nat.mod_eq_of_lt]

theorem matches_iff {R : InstructionRow} (hword : R.b < 2^w) (z : Instr 0 p r k) :
    «matches» R z ↔ decodeRow w p r k R = some (instantiate z (Fin.ofNat _ R.b)) := by
  refine ⟨decode_of_matches hword z, fun h => ?_⟩
  simpa only [erase_instantiate] using matches_erase_of_decode h

/-- Recover the decoded instruction by filling its erased shape from the literal field. -/
theorem instantiate_erase_of_decode {R : InstructionRow} (hword : R.b < 2^w)
    {i : Instr w p r k} (h : decodeRow w p r k R = some i) :
    instantiate (erase i) (Fin.ofNat _ R.b) = i :=
  Option.some.inj ((decode_of_matches hword (erase i) (matches_erase_of_decode h)).symm.trans h)

end ThreeFlat.Diagonal.TraceDecodeShape

end OAI

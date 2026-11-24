import OAI.Computability.VPVNP.EvaluatorTail

/-!
# Finite configurations on a live evaluator cut

The two-way tapes in `UniversalMachine.Config` use head-relative coordinates.
The field for each tape on a cut records its cells at offsets `-M,…,M`, with
the head at position `M`. Cells outside the field are blank. A running state
carries both fields. Acceptance and rejection each have a single representation,
independent of the tape contents at the halt.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorEncoding

open UniversalMachine

/-- A finite field of cells, with its head at index `M`. -/
@[ext] structure TapeWindow (M : ℕ) where
  /-- The symbols at offsets from minus the radius through plus the radius, with the head in
  the central cell. -/
  cells : Fin (2 * M + 1) → Symbol
  deriving DecidableEq

/-- Every cell outside the indicated head-relative interval is blank. -/
def TapeFits (M : ℕ) (t : Turing.Tape Symbol) : Prop :=
  ∀ j : ℤ, j < -(M : ℤ) ∨ (M : ℤ) < j → t.nth j = 0

variable {M extra : ℕ}

/-- Read a head-relative window of the specified radius from a two-way tape. -/
def TapeWindow.ofTape (M : ℕ) (t : Turing.Tape Symbol) : TapeWindow M where
  cells i := t.nth ((i.val : ℤ) - M)

/-- Extend the array on both sides by blanks. Each half tape begins
at the cell nearest the head. -/
def TapeWindow.toTape (t : TapeWindow M) : Turing.Tape Symbol where
  head := t.cells ⟨M, by omega⟩
  left := Turing.ListBlank.mk (List.ofFn fun i : Fin M => t.cells ⟨M - (i + 1), by omega⟩)
  right := Turing.ListBlank.mk (List.ofFn fun i : Fin M => t.cells ⟨M + (i + 1), by omega⟩)

/-- The window indexed by the signed displacement from its head. -/
def TapeWindow.read (t : TapeWindow M) (j : ℤ) : Symbol :=
  if h : -(M : ℤ) ≤ j ∧ j ≤ (M : ℤ) then t.cells ⟨(j + M).toNat, by omega⟩ else 0

private theorem half_nth (f : Fin M → Symbol) (n : ℕ) :
    (Turing.ListBlank.mk (List.ofFn f)).nth n = if h : n < M then f ⟨n, h⟩ else 0 := by
  rw [Turing.ListBlank.nth_mk]
  by_cases h : n < M
  · rw [dite_eq_left h, List.getI_eq_getElem _ (by simpa using h), List.getElem_ofFn]
  · rw [dite_eq_right h, List.getI_eq_default _ (by simpa using Nat.le_of_not_gt h)]
    rfl

theorem TapeWindow.toTape_nth (t : TapeWindow M) (j : ℤ) :
    t.toTape.nth j = t.read j := by
  cases j with
  | ofNat n =>
    cases n with
    | zero =>
      change t.cells _ = t.read 0
      unfold read
      rw [dite_eq_left (by omega)]
      congr 2; omega
    | succ n =>
      change (Turing.ListBlank.mk (List.ofFn _)).nth n = t.read ((n : ℤ) + 1)
      rw [half_nth]
      unfold read
      split_ifs <;> first | rfl | omega | (apply congrArg t.cells; apply Fin.ext; dsimp; omega)
  | negSucc n =>
    change (Turing.ListBlank.mk (List.ofFn _)).nth n = t.read (-((n : ℤ) + 1))
    rw [half_nth]
    unfold read
    split_ifs <;> first | rfl | omega | (apply congrArg t.cells; apply Fin.ext; dsimp; omega)

@[simp] theorem TapeWindow.read_index (t : TapeWindow M) (i : Fin (2 * M + 1)) :
    t.read ((i.val : ℤ) - M) = t.cells i := by
  unfold read
  rw [dite_eq_left (by omega)]
  congr 2; omega

theorem TapeWindow.toTape_fits (t : TapeWindow M) : TapeFits M t.toTape := by
  intro j hj
  rw [toTape_nth, read, dite_eq_right (by omega)]

@[simp] theorem TapeWindow.ofTape_toTape (t : TapeWindow M) :
    ofTape M t.toTape = t := by
  apply TapeWindow.ext
  funext i
  exact (t.toTape_nth _).trans (t.read_index i)

/-- Extensionality in signed head-relative coordinates. -/
theorem tape_ext {s t : Turing.Tape Symbol} (h : ∀ j : ℤ, s.nth j = t.nth j) : s = t := by
  have hh : s.head = t.head := h 0
  have hl : s.left = t.left := Turing.ListBlank.ext fun n => h (.negSucc n)
  have hr : s.right = t.right := Turing.ListBlank.ext fun n => h (.ofNat (n + 1))
  cases s
  cases t
  congr

@[simp] theorem TapeWindow.toTape_ofTape (t : Turing.Tape Symbol) (h : TapeFits M t) :
    (ofTape M t).toTape = t := by
  apply tape_ext
  intro j
  rw [toTape_nth, read]
  split
  · rename_i hj
    change t.nth (((j + M).toNat : ℤ) - M) = _
    congr 1; omega
  · exact (h j (by omega)).symm

/-- The bounded data of one running evaluator. -/
@[ext] structure ConfigWindow (extra M : ℕ) where
  /-- The finite control state stored alongside the two tape windows. -/
  state : Fin (extra + 2)
  /-- The first tape's symbols in the finite window around its head. -/
  firstTape : TapeWindow M
  /-- The second tape's symbols in the finite window around its head. -/
  secondTape : TapeWindow M
  deriving DecidableEq

/-- Recover a machine configuration by extending both stored windows with blank symbols outside
their bounds. -/
def ConfigWindow.toConfig (c : ConfigWindow extra M) : Config extra :=
  ⟨c.state, c.firstTape.toTape, c.secondTape.toTape⟩

/-- Record the control state and the two radius-bounded tape windows of a machine
configuration. -/
def ConfigWindow.ofConfig (M : ℕ) (c : Config extra) : ConfigWindow extra M :=
  ⟨c.state, TapeWindow.ofTape M c.firstTape, TapeWindow.ofTape M c.secondTape⟩

/-- Both tapes of the configuration are blank outside the specified radius of their heads. -/
def ConfigFits (M : ℕ) (c : Config extra) : Prop :=
  TapeFits M c.firstTape ∧ TapeFits M c.secondTape

@[simp] theorem ConfigWindow.ofConfig_toConfig (c : ConfigWindow extra M) :
    ofConfig M c.toConfig = c := by
  cases c
  simp [ofConfig, toConfig]

@[simp] theorem ConfigWindow.toConfig_ofConfig (c : Config extra) (h : ConfigFits M c) :
    (ofConfig M c).toConfig = c := by
  cases c
  simp [ofConfig, toConfig, h.1, h.2]

theorem ConfigWindow.toConfig_fits (c : ConfigWindow extra M) : ConfigFits M c.toConfig :=
  ⟨c.firstTape.toTape_fits, c.secondTape.toTape_fits⟩

/-- A live cut has a unique code for either kind of halt. -/
inductive Code (extra M : ℕ) where
  | accepted
  | rejected
  | running (c : ConfigWindow extra M) (hr : 2 ≤ c.state.val)
  deriving DecidableEq

/-- Interpret a finite cut code as an evaluator state, preserving its halt status or
reconstructing its running configuration. -/
def Code.toState : Code extra M → EvaluatorTail.State extra
  | .accepted => .accepted
  | .rejected => .rejected
  | .running c _ => .running c.toConfig

/-- Canonical bounded states use the two halting constructors exclusively
and retain the complete finite-support tapes in every running state. -/
def StateFits (M : ℕ) : EvaluatorTail.State extra → Prop
  | .accepted | .rejected => True
  | .running c => 2 ≤ c.state.val ∧ ConfigFits M c

/-- Encode a fitting evaluator state on a cut, using canonical halt codes and bounded windows
for a running state. -/
def Code.ofState (s : EvaluatorTail.State extra) (h : StateFits M s) : Code extra M :=
  match s with
  | .accepted => .accepted
  | .rejected => .rejected
  | .running c => .running (ConfigWindow.ofConfig M c) h.1

theorem Code.toState_fits (s : Code extra M) : StateFits M s.toState := by
  cases s with
  | accepted | rejected => trivial
  | running c hr => exact ⟨hr, c.toConfig_fits⟩

/-- Forgetting the serialization data identifies precisely the canonical
bounded states, including early halts and a zero-radius window. -/
def codeEquiv (extra M : ℕ) : Code extra M ≃ {s : EvaluatorTail.State extra // StateFits M s} where
  toFun s := ⟨s.toState, s.toState_fits⟩
  invFun s := Code.ofState s.val s.property
  left_inv s := by cases s <;> simp [Code.ofState, Code.toState]
  right_inv s := by
    rcases s with ⟨s, h⟩
    apply Subtype.ext
    cases s with
    | accepted | rejected => rfl
    | running c => simp [Code.ofState, Code.toState, h.2]

/-- One state word and two consecutive fixed-width tape fields. -/
def fieldWords (M : ℕ) : ℕ := 1 + (2 * M + 1) + (2 * M + 1)

/-- The control-state field at word zero of the serialized configuration. -/
def stateField (M : ℕ) : Fin (fieldWords M) := ⟨0, by unfold fieldWords; omega⟩

/-- The serialized word position of a first-tape cell, immediately following the control state. -/
def firstField (i : Fin (2 * M + 1)) : Fin (fieldWords M) :=
  ⟨1 + i, by unfold fieldWords; omega⟩

/-- The serialized word position of a second-tape cell, following the control state and all
first-tape cells. -/
def secondField (i : Fin (2 * M + 1)) : Fin (fieldWords M) :=
  ⟨1 + (2 * M + 1) + i, by unfold fieldWords; omega⟩

/-- The control field is the machine's own state number. -/
def Code.stateWord (c : Code extra M) : Fin (extra + 2) :=
  match c with
  | .rejected => ⟨0, by omega⟩
  | .accepted => ⟨1, by omega⟩
  | .running r _ => r.state

/-- Read a first-tape symbol from a cut code, using blank for either canonical halt. -/
def Code.firstCell (c : Code extra M) (i : Fin (2 * M + 1)) : Symbol :=
  match c with
  | .running r _ => r.firstTape.cells i
  | .accepted | .rejected => 0

/-- Read a second-tape symbol from a cut code, using blank for either canonical halt. -/
def Code.secondCell (c : Code extra M) (i : Fin (2 * M + 1)) : Symbol :=
  match c with
  | .running r _ => r.secondTape.cells i
  | .accepted | .rejected => 0

variable {w : ℕ}

private theorem symbolFits (hw : 2 ≤ w) : 3 ≤ 2 ^ w :=
  (by decide : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by decide : 0 < 2) hw)

/-- Store the state, then the first tape and the second tape in increasing
cell order. The halt codes zero every tape field. -/
def words (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) (c : Code extra M)
    (k : Fin (fieldWords M)) : BurstRAM.Word w :=
  if hz : k.val = 0 then (c.stateWord).castLE hs
  else if hf : k.val < 1 + (2 * M + 1) then
    (c.firstCell ⟨k.val - 1, by omega⟩).castLE (symbolFits hw)
  else (c.secondCell ⟨k.val - (1 + (2 * M + 1)), by
    have hk := k.isLt
    unfold fieldWords at hk
    omega⟩).castLE (symbolFits hw)

@[simp] theorem words_state (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) (c : Code extra M) :
    (words hw hs c (stateField M)).val = c.stateWord.val := by
  simp [words, stateField]

@[simp] theorem words_first (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) (c : Code extra M)
    (i : Fin (2 * M + 1)) : (words hw hs c (firstField i)).val = (c.firstCell i).val := by
  simp [words, firstField, show i.val ≤ 2 * M by omega]

@[simp] theorem words_second (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) (c : Code extra M)
    (i : Fin (2 * M + 1)) : (words hw hs c (secondField i)).val = (c.secondCell i).val := by
  simp [words, secondField]

private def parseCell (x : BurstRAM.Word w) : Symbol := ⟨x.val % 3, Nat.mod_lt _ (by decide)⟩

private def parseWords (a : Fin (fieldWords M) → BurstRAM.Word w) : Code extra M :=
  let state := (a (stateField M)).val
  if state = 1 then .accepted else
  if h : 2 ≤ state ∧ state < extra + 2 then
    .running ⟨⟨state, h.2⟩, ⟨fun i => parseCell (a (firstField i))⟩,
      ⟨fun i => parseCell (a (secondField i))⟩⟩ h.1
  else .rejected

/-- The checked binary decoder requires canonical symbols and zeroes at every
unused position. There are exactly `fieldWords M * w` bits on the field. -/
def format (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) :
    RAMSerialization.Format w (fieldWords M) (Code extra M) where
  words := words hw hs
  parse := parseWords
  parse_words c := by
    cases c with
    | accepted | rejected => simp [parseWords, Code.stateWord]
    | running c hr =>
      have hne : c.state.val ≠ 1 := by omega
      have hlt := c.state.isLt
      simp only [parseWords, words_state, Code.stateWord, hne, ↓reduceIte, hr, hlt, and_self,
        ↓reduceDIte]
      congr 1
      apply ConfigWindow.ext
      · rfl
      · apply TapeWindow.ext
        funext i
        apply Fin.ext
        simp [parseCell, Code.firstCell, Nat.mod_eq_of_lt (c.firstTape.cells i).isLt]
      · apply TapeWindow.ext
        funext i
        apply Fin.ext
        simp [parseCell, Code.secondCell, Nat.mod_eq_of_lt (c.secondTape.cells i).isLt]

theorem decode_iff (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) (c : Code extra M)
    (b : CutSchedule.Bits (fieldWords M * w)) :
    (format hw hs).decode b = some c ↔ b = (format hw hs).encode c :=
  RAMSerialization.Format.decode_iff ..

/-- Bounded evaluator configurations, including the two canonical halts,
are in bijection with all valid bit strings of the allocated width. -/
def stateBitsEquiv (M : ℕ) (hw : 2 ≤ w) (hs : extra + 2 ≤ 2 ^ w) :
    {s : EvaluatorTail.State extra // StateFits M s} ≃ {b // ((format (M := M) hw hs).decode b).isSome} :=
  (codeEquiv extra M).symm.trans (format hw hs).canonicalEquiv

end LiveEvaluatorEncoding

end VPVNP
end Computability
end OAI

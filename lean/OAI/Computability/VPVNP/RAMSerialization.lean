import OAI.Computability.VPVNP.RAMLayout
import OAI.Computability.VPVNP.RAMWordBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Binary messages of the RAM transcript

Lemma 10.1 sends an eight-word successor message and a block of `4H`
five-word records at each cross-site sorting layer. Each word occupies exactly
`w` bits in little-endian order. The parsers below decode fixed-size fields and
check the input against the canonical encoding. This rejects unknown tags,
nonzero padding, and nonzero state fields for halted calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSerialization

open BurstRAM RAMMemory

/-- Least significant bit first. -/
def wordBits (w : ℕ) : Word w ≃ (Fin w → Bool) :=
  finFunctionFinEquiv.symm.trans ((Equiv.refl _).arrowCongr finTwoEquiv)

/-- Concatenate `k` fixed-width words in their given order. -/
def arrayBits (k w : ℕ) : (Fin k → Word w) ≃ (Fin (k * w) → Bool) :=
  (((Equiv.refl _).arrowCongr (wordBits w)).trans (Equiv.curry _ _ _).symm).trans
    (finProdFinEquiv.arrowCongr (Equiv.refl _))

variable {w k : ℕ}

theorem arrayBits_at (a : Fin k → Word w) (i : Fin k) (j : Fin w) :
    arrayBits k w a (finProdFinEquiv (i, j)) = wordBits w (a i) j := by
  simp [arrayBits, Equiv.curry]

theorem wordBits_zero (j : Fin w) : wordBits w 0 j = false := by
  change (finFunctionFinEquiv.symm (0 : Word w) j == 1) = false
  have hz : finFunctionFinEquiv.symm (0 : Word w) j = 0 := by
    apply Fin.ext
    simp [finFunctionFinEquiv_symm_apply_val]
  simp [hz]

/-- Natural-valued records from the trace, with their word range enforced
for all three counter/address fields. -/
structure WordRecord (w : ℕ) where
  /-- Whether this serialized record describes initialization, an external read, or an external
  write. -/
  kind : Kind
  /-- External word address of the recorded initialization or probe. -/
  address : Word w
  /-- Word initialized, returned by a read, or supplied to a write. -/
  value : Word w
  /-- Word-sized start-cost field used with the ordinal to order probes from the same address. -/
  startCost : Word w
  /-- Word-sized ordinal giving a probe’s position among the external accesses in its call. -/
  ordinal : Word w
  deriving DecidableEq

/-- Widen the address, start cost, and ordinal to natural numbers to obtain the memory record
used by the ordering and read checks. -/
def WordRecord.record (r : WordRecord w) : Record (Word w) :=
  ⟨r.kind, r.address.val, r.value, r.startCost.val, r.ordinal.val⟩

/-- Convert a memory record to word fields using bounds on its address, start cost, and
ordinal. -/
def WordRecord.ofRecord (r : Record (Word w))
    (h : RecordFitsWord r) : WordRecord w :=
  ⟨r.kind, ⟨r.address, h.1⟩, r.value, ⟨r.startCost, h.2.1⟩, ⟨r.ordinal, h.2.2⟩⟩

@[simp] theorem WordRecord.ofRecord_record (r : Record (Word w)) (h) :
    (WordRecord.ofRecord r h).record = r := rfl

theorem WordRecord.record_injective : Function.Injective (WordRecord.record (w := w)) := by
  rintro ⟨_, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩⟩ ⟨_, ⟨_, _⟩, _, ⟨_, _⟩, ⟨_, _⟩⟩ h
  cases h
  rfl

/-- A fixed-length word format with a left inverse. On arbitrary bit strings the
public decoder checks that re-encoding reproduces every bit. -/
structure Format (w k : ℕ) (α : Type*) where
  /-- The fixed array of width-w words that canonically represents a message. -/
  words : α → Fin k → Word w
  /-- Recover a candidate message from a fixed word array, with exact recovery on arrays
  produced by the encoder. -/
  parse : (Fin k → Word w) → α
  parse_words : ∀ a, parse (words a) = a

variable {α : Type*}

/-- Concatenate the message’s word fields in order, with each field written least significant
bit first. -/
def Format.encode (f : Format w k α) (a : α) : Fin (k * w) → Bool := arrayBits k w (f.words a)

/-- Parse the input bits as a word array and accept the resulting message exactly when
re-encoding it reproduces the input. -/
def Format.decode (f : Format w k α) (b : Fin (k * w) → Bool) : Option α :=
  let x := f.parse ((arrayBits k w).symm b)
  if f.encode x = b then some x else none

theorem Format.decode_iff (f : Format w k α) (b : Fin (k * w) → Bool) (x : α) :
    f.decode b = some x ↔ b = f.encode x := by
  constructor
  · simp only [Format.decode]
    split
    · rename_i h
      intro he
      cases he
      exact h.symm
    · simp
  · rintro rfl
    simp [Format.decode, Format.encode, f.parse_words]

theorem Format.encode_injective (f : Format w k α) : Function.Injective f.encode := by
  intro x y h
  exact Option.some.inj (((f.decode_iff _ x).2 rfl).symm.trans ((f.decode_iff _ y).2 h))

/-- The valid binary patterns are in bijection with the typed messages. -/
def Format.canonicalEquiv (f : Format w k α) : α ≃ {b // (f.decode b).isSome} where
  toFun a := ⟨f.encode a, by rw [(f.decode_iff _ a).2 rfl]; rfl⟩
  invFun b := (f.decode b.val).get b.property
  left_inv a := by
    apply Option.some.inj
    exact (Option.some_get _).trans ((f.decode_iff _ a).2 rfl)
  right_inv b := Subtype.ext ((f.decode_iff _ _).mp (Option.some_get _).symm).symm

private def kindTag : Kind → Fin 4
  | .init => 1
  | .read => 2
  | .write => 3

private def tagWord (hw : 2 ≤ w) (tag : Fin 4) : Word w :=
  ⟨tag.val, tag.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hw)⟩

/-- `(kind, address, value, start cost, ordinal)`. The all-zero tuple alone
encodes the empty record. The other tags are 1 for init, 2 for read, 3 for write. -/
def recordFormat (hw : 2 ≤ w) : Format w 5 (Option (WordRecord w)) where
  words
    | none => fun _ ↦ 0
    | some r => ![tagWord hw (kindTag r.kind), r.address, r.value, r.startCost, r.ordinal]
  parse a :=
    let mk := fun k ↦ some (WordRecord.mk k (a 1) (a 2) (a 3) (a 4))
    match (a 0).val with
    | 1 => mk .init
    | 2 => mk .read
    | 3 => mk .write
    | _ => none
  parse_words := by
    rintro (_ | ⟨k, a, v, c, j⟩)
    · rfl
    · cases k <;> rfl

theorem recordFormat_empty (hw : 2 ≤ w) : (recordFormat hw).encode none = fun _ ↦ false := by
  funext i
  obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective i
  exact (arrayBits_at _ j t).trans (wordBits_zero t)

/-- Consecutive copies of the same format. Each record occupies its own
complete five-word interval in a sorting block. -/
def Format.replicate (f : Format w k α) (m : ℕ) : Format w (m * k) (Fin m → α) where
  words a i :=
    let p := finProdFinEquiv.symm i
    f.words (a p.1) p.2
  parse a i := f.parse (fun j ↦ a (finProdFinEquiv (i, j)))
  parse_words a := by
    funext i
    simp [f.parse_words]

/-- Format for a sorting block of 4H slots, each occupying five words and holding either a word
record or canonical padding. -/
def blockFormat (H : ℕ) (hw : 2 ≤ w) : Format w (4 * H * 5) (Fin (4 * H) → Option (WordRecord w)) :=
  (recordFormat hw).replicate (4 * H)

theorem block_decode_iff (H : ℕ) (hw : 2 ≤ w) (b : Fin (RAMLayout.blockBits H w) → Bool)
    (r : Fin (4 * H) → Option (WordRecord w)) :
    (blockFormat H hw).decode b = some r ↔ b = (blockFormat H hw).encode r :=
  Format.decode_iff ..

/-- Narrow a padded slot once its three natural-valued fields have been
checked against the word width. -/
def narrowSlot (r : Option (Record (Word w))) (h : ∀ t ∈ r, RecordFitsWord t) :
    Option (WordRecord w) :=
  match r with
  | none => none
  | some t => some (WordRecord.ofRecord t (h t rfl))

@[simp] theorem widen_narrowSlot (r : Option (Record (Word w))) (h) :
    (narrowSlot r h).map WordRecord.record = r := by cases r <;> rfl

private theorem widenSlot_injective :
    Function.Injective (Option.map (WordRecord.record (w := w))) := by
  intro x y h
  cases x <;> cases y <;> simp_all [WordRecord.record_injective.eq_iff]

/-- Decoding a block produces the same padded-record type that the network sorts. -/
def decodeBlock (H : ℕ) (hw : 2 ≤ w) (b : Fin (RAMLayout.blockBits H w) → Bool) :
    Option (Fin (4 * H) → Option (Record (Word w))) :=
  ((blockFormat H hw).decode b).map fun a i ↦ (a i).map WordRecord.record

/-- Every representable sorting block has just one accepted bit pattern. -/
theorem decodeBlock_iff (H : ℕ) (hw : 2 ≤ w) (r : Fin (4 * H) → Option (Record (Word w)))
    (hr : ∀ i t, t ∈ r i → RecordFitsWord t) (b : Fin (RAMLayout.blockBits H w) → Bool) :
    decodeBlock H hw b = some r ↔
      b = (blockFormat H hw).encode (fun i ↦ narrowSlot (r i) (hr i)) := by
  rw [decodeBlock, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    have he : a = fun i ↦ narrowSlot (r i) (hr i) := by
      funext i
      apply widenSlot_injective
      exact (congrFun h i).trans (widen_narrowSlot _ _).symm
    rw [← he]
    exact (block_decode_iff H hw _ _).mp ha
  · intro h
    exact ⟨_, (block_decode_iff H hw _ _).mpr h, funext fun i ↦ widen_narrowSlot _ _⟩

/-- In a capped run the representability condition follows from membership
in the padded input array. It therefore holds in every permuted intermediate
sorting array. -/
theorem permuted_block_encoding {S H : ℕ} (hw : 2 ≤ w) (header : ℕ → Word w)
    {rs : List (Report w)} {out : List (Option (Record (Word w)))}
    (hH : 0 < H) (hc : RAMBuckets.cost Report.probes rs ≤ S * H) (hword : S * H < 2 ^ w)
    (hp : (canonicalRecordBlocks header S H rs).flatten.Perm out)
    (r : Fin (4 * H) → Option (Record (Word w))) (hm : ∀ i, r i ∈ out) :
    ∃! b, decodeBlock H hw b = some r := by
  have hr (i : Fin (4 * H)) (t : Record (Word w)) (ht : t ∈ r i) : RecordFitsWord t :=
    perm_canonicalRecordBlocks_fitsWord header hH hc hword hp (ht ▸ hm i)
  exact ⟨_, (decodeBlock_iff H hw r hr _).2 rfl, fun _ h ↦ (decodeBlock_iff H hw r hr _).1 h⟩

/-- The paper sets `w = (r+10)^4`, where `r = B ⌈log₂ n⌉`. A polynomial
site/call budget gives `d+e = log₂ (SH) ≤ K(r+1)` for some fixed `K`.
Already at `r+1 ≥ K`, all four tags and the final cost `SH` fit. -/
theorem word_capacity (r d e K : ℕ) (hsize : d + e ≤ K * (r + 1)) (hr : K ≤ r + 1) :
    2 ≤ (r + 10) ^ 4 ∧ 2 ^ d * 2 ^ e < 2 ^ ((r + 10) ^ 4) := by
  have hpow : 2 ≤ (r + 10) ^ 4 := by
    calc
      2 ≤ 10 ^ 4 := by decide
      _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  refine ⟨hpow, ?_⟩
  rw [← pow_add]
  apply Nat.pow_lt_pow_right (by decide)
  have hquad := hsize.trans (Nat.mul_le_mul_right (r + 1) hr)
  calc
    d + e ≤ (r + 1) ^ 2 := by simpa [pow_two] using hquad
    _ < (r + 10) ^ 2 := Nat.pow_lt_pow_left (by omega) (by decide)
    _ ≤ (r + 10) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)

/-- The status distinguishes a running state word from an accepted halt.
The actual cumulative cost may equal the global cap. -/
structure Successor (w cap : ℕ) where
  /-- Persistent word passed to a running successor, or the empty option for an accepted halt. -/
  state : Option (Word w)
  /-- Cumulative cost transmitted across the site boundary, bounded inclusively by the global
  cap. -/
  cost : Fin (cap + 1)
  /-- Last padded slot of the sender’s sorted block, transmitted for the predecessor check
  across the site boundary. -/
  lastRecord : Option (WordRecord w)

variable {cap : ℕ}

private def controlWords (hw : 2 ≤ w) (hc : cap < 2 ^ w) (s : Successor w cap) : Fin 3 → Word w :=
  ![tagWord hw (if s.state.isSome then 1 else 2),
    ⟨s.cost.val, lt_of_le_of_lt (Nat.le_of_lt_succ s.cost.isLt) hc⟩, s.state.getD 0]

/-- `(status, cost, state)` followed by the last sorted record. Status 1 means
running and 2 means accepted. On a halt the state word is zero. The whole cost,
including a final cost exactly `SH`, fits when `SH < 2^w`. -/
def successorFormat (hw : 2 ≤ w) (hc : cap < 2 ^ w) : Format w 8 (Successor w cap) where
  words s := Fin.append (controlWords hw hc s) ((recordFormat hw).words s.lastRecord)
  parse a :=
    let status := a (Fin.castAdd 5 (0 : Fin 3))
    let cost := a (Fin.castAdd 5 (1 : Fin 3))
    let state := a (Fin.castAdd 5 (2 : Fin 3))
    ⟨if status.val = 1 then some state else none,
      if h : cost.val ≤ cap then ⟨cost.val, Nat.lt_succ_of_le h⟩ else 0,
      (recordFormat hw).parse (fun i ↦ a (Fin.natAdd 3 i))⟩
  parse_words := by
    rintro ⟨state, cost, last⟩
    have h := Nat.le_of_lt_succ cost.isLt
    simp only [Fin.append_left, Fin.append_right, Format.parse_words]
    cases state <;> simp [controlWords, tagWord, h]

theorem successor_decode_iff (hw : 2 ≤ w) (hc : cap < 2 ^ w) (b : Fin (8 * w) → Bool)
    (s : Successor w cap) :
    (successorFormat hw hc).decode b = some s ↔ b = (successorFormat hw hc).encode s :=
  Format.decode_iff ..

/-- The prescribed all-zero end field cannot be misread as a successor
message. A validator handles the boundary locally using its site identifier. -/
theorem clamped_successor (hw : 2 ≤ w) (hc : cap < 2 ^ w) :
    (successorFormat hw hc).decode (fun _ ↦ false) = none := by
  cases h : (successorFormat hw hc).decode (fun _ ↦ false) with
  | none => rfl
  | some s =>
    have he := (successor_decode_iff hw hc _ s).mp h
    have hz : arrayBits 8 w (fun _ ↦ 0) = fun _ ↦ false := by
      funext i
      obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective i
      exact (arrayBits_at _ j t).trans (wordBits_zero t)
    have heq := (arrayBits 8 w).injective (hz.trans he)
    have htag := congrArg (fun f : Fin 8 → Word w ↦ (f (Fin.castAdd 5 (0 : Fin 3))).val) heq
    change 0 = (tagWord hw (if s.state.isSome then 1 else 2)).val at htag
    cases hs : s.state <;> simp [hs, tagWord] at htag

end RAMSerialization

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.MotifDemandPadding
import OAI.Computability.VPVNP.MotifPayload
import OAI.Computability.VPVNP.MotifParameters
import Mathlib.Data.Nat.Bitwise

/-!
# Reading the entries of a grouped motif map

For the construction on page 21, the input at a party is a collection of
incident bit strings. Read their common selector sequence, check its full
width vector, then use each copy's demand and supply fields to look up one
parameter. The output list records multiplicities in the resulting monomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifEntry

open MotifSelector

/-- Binary digits are numbered from the least significant end. -/
def inputBits {w : ℕ} (x : Fin (2 ^ w)) (i : Fin w) : Bool := x.val.testBit i.val

/-- Probe one position, returning a zero bit outside the supplied string. -/
def paddedBit {w : ℕ} (bits : Fin w → Bool) (pos : ℕ) : Bool :=
  if h : pos < w then bits ⟨pos, h⟩ else false

@[simp] theorem paddedBit_inputBits {w : ℕ} (x : Fin (2 ^ w)) (pos : ℕ) :
    paddedBit (inputBits x) pos = x.val.testBit pos := by
  by_cases h : pos < w
  · simp [paddedBit, inputBits, h]
  · have hx : x.val < 2 ^ pos := x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [paddedBit, h, Nat.testBit_eq_false_of_lt hx]

/-- Read consecutive bits by incrementing the probe position and combining
each bit with the remaining high part by one shift and one addition. -/
def readField {w : ℕ} (bits : Fin w → Bool) (off : ℕ) : ℕ → ℕ
  | 0 => 0
  | a + 1 => (paddedBit bits off).toNat + 2 * readField bits (off + 1) a

/-- The input oracle is used only at the indicated little-endian positions. -/
theorem readField_eq_sum {w : ℕ} (bits : Fin w → Bool) (off a : ℕ) :
    readField bits off a = ∑ i : Fin a, (paddedBit bits (off + i.val)).toNat * 2 ^ i.val := by
  induction a generalizing off with
  | zero => simp [readField]
  | succ a ih =>
    rw [readField, ih, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, Nat.add_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show off + 1 + i.val = off + (i.val + 1) by omega]
    ac_rfl

private theorem testBit_toNat_eq (n pos : ℕ) :
    (n.testBit pos).toNat = n / 2 ^ pos % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : n / 2 ^ pos % 2 = 1
  · simp [h]
  · have hz : n / 2 ^ pos % 2 = 0 := by omega
    simp [hz]

/-- Decoding from the bit oracle gives the same digit as division and
remainder, even if the requested field is wholly or partly in the padding. -/
theorem readField_inputBits {w : ℕ} (x : Fin (2 ^ w)) (off a : ℕ) :
    readField (inputBits x) off a = (x.val / 2 ^ off) % 2 ^ a := by
  induction a generalizing off with
  | zero => simp [readField, Nat.mod_one]
  | succ a ih =>
    rw [readField, paddedBit_inputBits, testBit_toNat_eq, ih, pow_succ' 2 a,
      Nat.mod_mul, Nat.div_div_eq_div_mul, pow_succ 2 off]

/-- The decoded value of an arbitrary field fits in the field width. -/
theorem readField_lt {w : ℕ} (bits : Fin w → Bool) (off a : ℕ) :
    readField bits off a < 2 ^ a := by
  induction a generalizing off with
  | zero => simp [readField]
  | succ a ih =>
    have hh := ih (off + 1)
    rw [readField, pow_succ]
    cases paddedBit bits off <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- A typed field, suitable for indexing the table of a fixed base motif. -/
def fieldIndex {w : ℕ} (bits : Fin w → Bool) (off a : ℕ) : Fin (2 ^ a) :=
  ⟨readField bits off a, readField_lt bits off a⟩

/-- Reading the indicated demand chunk agrees with the padding injection. -/
theorem fieldIndex_eq_padFields {w u a : ℕ} (h : w ≤ u * a) (x : Fin (2 ^ w)) (i : Fin u) :
    fieldIndex (inputBits x) (a * i.val) a = MotifDemandPadding.padFields h x i := by
  apply Fin.ext
  rw [MotifDemandPadding.padFields_digit, ← pow_mul, ← readField_inputBits]
  rfl

/-- Record each probe and the fixed operations in the recursion.
Each nonempty field iteration pays for the width test, one padded probe,
the position increment, low-bit conversion, doubling, and addition. -/
def meteredField {w : ℕ} (bits : Fin w → Bool) (off : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | a + 1 =>
    let hi := meteredField bits (off + 1) a
    ((paddedBit bits off).toNat + 2 * hi.1, 6 + hi.2)

theorem meteredField_spec {w : ℕ} (bits : Fin w → Bool) (off a : ℕ) :
    meteredField bits off a = (readField bits off a, 6 * a + 1) := by
  induction a generalizing off with
  | zero => simp [meteredField, readField]
  | succ a ih =>
    simp only [meteredField, ih, readField, Nat.mul_succ]
    congr 1
    omega


/-- Locate one selector above the payload. -/
def readTag {u bits v : ℕ} (x : Fin (v + u * bits) → Bool) (i : Fin u) : Word bits :=
  fieldIndex x (v + bits * i.val) bits

theorem readTag_inputBits {u bits v : ℕ} (x : Word (v + u * bits)) (i : Fin u) :
    readTag (inputBits x) i = (wireFields u bits v x).1 i := by
  apply Fin.ext
  change readField (inputBits x) _ _ = x.val / 2 ^ v / (2 ^ bits) ^ i.val % 2 ^ bits
  rw [readField_inputBits, Nat.div_div_eq_div_mul, pow_add 2 v (bits * i.val), pow_mul 2 bits i.val]

/-- The low bits of a supply coordinate are its payload. -/
def payloadBits {u bits v : ℕ} (x : Fin (v + u * bits) → Bool) : Fin v → Bool :=
  fun i => x (Fin.castLE (Nat.le_add_right _ _) i)

theorem payloadBits_inputBits {u bits v : ℕ} (x : Word (v + u * bits)) :
    payloadBits (inputBits x) = inputBits (wireFields u bits v x).2 := by
  funext i
  change x.val.testBit i.val = (x.val % 2 ^ v).testBit i.val
  simp [Nat.testBit_mod_two_pow, i.isLt]

/-- Scan the widths preceding a copy to find the start of its payload field. -/
def offset {u : ℕ} (w : Fin u → ℕ) (i : Fin u) : ℕ :=
  ∑ t : Fin i.val, w (Fin.castLE i.isLt.le t)

theorem fieldIndex_eq_unpack {u : ℕ} (w : Fin u → ℕ) (x : Word (∑ i, w i)) (i : Fin u) :
    fieldIndex (inputBits x) (offset w i) (w i) = unpackFields w x i := by
  apply Fin.ext
  change readField (inputBits x) _ _ = (x.val / ∏ j : Fin i.val,
    2 ^ w (Fin.castLE i.isLt.le j)) % (2 ^ w i)
  rw [readField_inputBits, Finset.prod_pow_eq_pow_sum]
  rfl

variable {J E S V : Type*} {C : J → Type*} {bits u : ℕ}

/-- The code table can be searched even when some bit patterns are unused. -/
def decode (table : List S) (code : S ↪ Word bits) (tag : Word bits) : Option S :=
  table.find? (fun s => decide (code s = tag))

theorem decode_eq_some (table : List S) (complete : ∀ s, s ∈ table)
    (code : S ↪ Word bits) (tag : Word bits) (s : S) :
    decode table code tag = some s ↔ code s = tag := by
  constructor
  · intro h
    simpa using List.find?_some h
  · intro hs
    cases h : decode table code tag with
    | none =>
      have hn := List.find?_eq_none.mp h s (complete s)
      simp [hs] at hn
    | some t =>
      have ht : code t = tag := by simpa using List.find?_some h
      rw [code.injective (ht.trans hs.symm)]

/-- Read the reference half-wire without using choice. -/
def anchor [DecidableEq J] (G : Supply J E) {I : E → Type*} (j : J) (x : Half G I j) :
    I (G.anchor j) :=
  if h : j = G.src (G.anchor j) then x.1 _ h else
    x.2 _ ((G.anchor_incident j).resolve_left fun he => h he.symm).symm

theorem anchor_eq_readAnchor [DecidableEq J] (G : Supply J E) {I : E → Type*}
    (j : J) (x : Half G I j) : anchor G j x = readAnchor G j x := by
  unfold anchor readAnchor
  split <;> simp_all

variable [DecidableEq J] [Fintype E]

/-- Check a party's source and target ports, testing one copy at a time. -/
def consistent (G : Supply J E) (j : J) (tags : Half G (fun _ => Fin u → Word bits) j) :
    Bool :=
  let t := anchor G j tags
  decide (∀ e, (if h : j = G.src e then ∀ i, tags.1 e h i = t i else True) ∧
    (if h : j = G.dst e then ∀ i, tags.2 e h i = t i else True))

private theorem consistent_iff {I : E → Type*} (G : Supply J E) (j : J)
    (fields : Half G (fun e => (Fin u → Word bits) × I e) j) :
    consistent G j (mapHalf G (fun _ => Prod.fst) fields) = true ↔ HalfAgrees G j fields := by
  have ha : anchor G j (mapHalf G (fun _ => Prod.fst) fields) = (readAnchor G j fields).1 := by
    rw [← anchor_eq_readAnchor]
    unfold anchor
    split <;> rfl
  unfold consistent
  dsimp only
  rw [decide_eq_true_iff, ha]
  unfold HalfAgrees
  constructor
  · intro h
    constructor
    · intro e he
      exact funext (by simpa [he, mapHalf] using (h e).1)
    · intro e he
      exact funext (by simpa [he, mapHalf] using (h e).2)
  · rintro ⟨hl, hr⟩ e
    constructor
    · split <;> rename_i he
      · exact fun i => congrFun (hl e he) i
      · trivial
    · split <;> rename_i he
      · exact fun i => congrFun (hr e he) i
      · trivial

/-- Decode the anchor sequence, checking each tag against the fixed selector
table. Once decoded, the array can be indexed when computing payload offsets. -/
def selectors? (table : List S) (code : S ↪ Word bits) (tags : Fin u → Word bits) :
    Option (Fin u → S) :=
  let a := Vector.ofFn (fun i => decode table code (tags i))
  if h : ∀ i : Fin u, (a[i.val]).isSome then
    some (fun i => (a[i.val]).get (h i)) else none

private theorem selectors_spec (table : List S) (complete : ∀ s, s ∈ table)
    (code : S ↪ Word bits) (tags : Fin u → Word bits) (θ : Fin u → S) :
    selectors? table code tags = some θ ↔ sequenceCode code u θ = tags := by
  simp only [selectors?, Vector.getElem_ofFn]
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact funext fun i => (decode_eq_some table complete code _ _).1 (Option.some_get (h i)).symm
    · intro he
      exact funext fun i => Option.get_of_eq_some _ ((decode_eq_some table complete code _ _).2
        (congrFun he i))
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun he => h fun i => Option.isSome_iff_exists.mpr
      ⟨θ i, (decode_eq_some table complete code _ _).2 (congrFun he i)⟩

/-- Read the local supply fields in copy order and check the total vector on
all edges. The last test also checks coordinates away from the current party. -/
def extract (G : Supply J E) (w : S → E → ℕ) (v : E → ℕ) (θ : Fin u → S)
    (j : J) (c : Fin u → C j) (x : Half G (fun e => Fin (v e) → Bool) j) :
    Option (EntryIndices G C w u j) :=
  if ∀ e, v e = totalWidth w θ e then
    some (fun i => ⟨θ i, c i, mapHalf G (fun e y =>
      fieldIndex y (offset (fun l => w (θ l) e) i) (w (θ i) e)) x⟩)
  else none

omit [DecidableEq J] in
private theorem extract_inputBits (G : Supply J E) (w : S → E → ℕ) (v : E → ℕ)
    (θ : Fin u → S) (j : J) (c : Fin u → C j) (x : Half G (fun e => Word (v e)) j) :
    extract G w v θ j c (mapHalf G (fun _ => inputBits) x) = payloadIndices G w v θ j c x := by
  unfold extract payloadIndices
  by_cases h : v = totalWidth w θ
  · subst v
    rw [ite_eq_left (fun _ => rfl), dite_eq_left rfl]
    apply congrArg some
    funext i
    congr 2
    apply Prod.ext
    · funext e he
      exact fieldIndex_eq_unpack _ _ i
    · funext e he
      exact fieldIndex_eq_unpack _ _ i
  · rw [ite_eq_right (fun he => h (funext he)), dite_eq_right h]

/-- Execute all the entry checks on bit-string inputs. The argument `c`
supplies the demand coordinate of each copy. -/
def indices (G : Supply J E) (w : S → E → ℕ) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J) (c : Fin u → C j)
    (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) : Option (EntryIndices G C w u j) :=
  let tags := mapHalf G (fun _ => readTag) x
  if consistent G j tags then
    (selectors? table code (anchor G j tags)).bind fun θ =>
      extract G w v θ j c (mapHalf G (fun _ => payloadBits) x)
  else none

/-- Correctness of the executable local parser against the grouped wire map. -/
theorem indices_eq_groupedIndices (G : Supply J E) (w : S → E → ℕ) (table : List S)
    (complete : ∀ s, s ∈ table) (code : S ↪ Word bits) (v : E → ℕ) (j : J)
    (c : Fin u → C j) (x : Half G (fun e => Word (v e + u * bits)) j) :
    indices G w table code v j c (mapHalf G (fun _ => inputBits) x) =
      groupedIndices G w code v j c x := by
  classical
  let fields := mapHalf G (fun e => wireFields u bits (v e)) x
  let tags := mapHalf G (fun _ => Prod.fst) fields
  let payload := mapHalf G (fun _ => Prod.snd) fields
  let t := (readAnchor G j fields).1
  have ht : mapHalf G (fun _ => readTag) (mapHalf G (fun _ => inputBits) x) = tags := by
    apply Prod.ext <;> funext e he i <;> exact readTag_inputBits _ i
  have hp : mapHalf G (fun _ => payloadBits) (mapHalf G (fun _ => inputBits) x) =
      mapHalf G (fun _ => inputBits) payload := by
    apply Prod.ext <;> funext e he <;> exact payloadBits_inputBits _
  have ha : anchor G j tags = t := by
    dsimp only [t]
    rw [← anchor_eq_readAnchor]
    unfold anchor
    split <;> rfl
  unfold indices groupedIndices
  dsimp only
  rw [ht, hp, ha]
  change (if consistent G j tags then _ else _) =
    (if HalfAgrees G j fields then tagIndices G w code v t j c payload else _)
  by_cases hag : HalfAgrees G j fields
  · rw [ite_eq_left hag, ite_eq_left ((consistent_iff G j fields).2 hag)]
    unfold tagIndices
    split
    · rename_i hr
      rw [(selectors_spec table complete code t hr.choose).2 hr.choose_spec]
      exact extract_inputBits _ _ _ _ _ _ _
    · rename_i hr
      cases hx : selectors? table code t with
      | none => rfl
      | some θ => exact (hr ⟨θ, (selectors_spec table complete code t θ).1 hx⟩).elim
  · rw [ite_eq_right hag, ite_eq_right (fun h => hag ((consistent_iff G j fields).1 h))]

/-- Replace the indices by their fixed parameter-table names. Repeated names
are retained once per occurrence. -/
def labels {G : Supply J E} {w : S → E → ℕ}
    (lookup : ∀ s j, C j → Half G (fun e => Word (w s e)) j → V) (j : J)
    (out : Option (EntryIndices G C w u j)) : Option (List V) :=
  out.map fun t => List.ofFn fun i => lookup (t i).1 j (t i).2.1 (t i).2.2

omit [DecidableEq J] [Fintype E] in
theorem labels_length {G : Supply J E} {w : S → E → ℕ}
    (lookup : ∀ s j, C j → Half G (fun e => Word (w s e)) j → V) (j : J)
    (out : Option (EntryIndices G C w u j)) {names : List V}
    (h : labels lookup j out = some names) : names.length = u := by
  cases out <;> simp [labels] at h
  simp [← h]

omit [DecidableEq J] [Fintype E] in
theorem eval_labels {R : Type*} [CommMonoidWithZero R] {G : Supply J E} {w : S → E → ℕ}
    (lookup : ∀ s j, C j → Half G (fun e => Word (w s e)) j → V) (κ : V → R) (j : J)
    (out : Option (EntryIndices G C w u j)) :
    (labels lookup j out).elim 0 (fun names => (names.map κ).prod) =
      evalIndices (fun s j c x => κ (lookup s j c x)) j out := by
  cases out <;> simp [labels, evalIndices, List.map_ofFn, List.prod_ofFn]

/-- Local demand inputs with one bit string on each incident half-wire. -/
abbrev DemandBits {D : Type*} (src dst : D → J) (b : D → ℕ) (j : J) :=
  ((e : D) → j = src e → Fin (b e) → Bool) × ((e : D) → j = dst e → Fin (b e) → Bool)

/-- Read a copy's fixed-size fields on the demand side, supplying zero bits
above the width of the desired demand. -/
def demandFields {D : Type*} (src dst : D → J) (a : D → ℕ) {b : D → ℕ}
    (i : Fin u) (j : J) (d : DemandBits src dst b j) : MotifDemandPadding.HalfBits src dst a j :=
  (fun e h => fieldIndex (d.1 e h) (a e * i.val) (a e),
   fun e h => fieldIndex (d.2 e h) (a e * i.val) (a e))

/-- Canonical bit strings for the two demand endpoints. -/
def demandBits {D : Type*} (src dst : D → J) {b : D → ℕ} (j : J)
    (d : MotifDemandPadding.HalfBits src dst b j) : DemandBits src dst b j :=
  (fun e h => inputBits (d.1 e h), fun e h => inputBits (d.2 e h))

omit [DecidableEq J] [Fintype E] in
theorem demandFields_eq {D : Type*} (src dst : D → J) {a b : D → ℕ}
    (hab : ∀ e, b e ≤ u * a e) (i : Fin u) (j : J)
    (d : MotifDemandPadding.HalfBits src dst b j) :
    demandFields src dst a i j (demandBits src dst j d) =
      MotifDemandPadding.demandChunk src dst hab i j d := by
  apply Prod.ext <;> funext e he <;> exact fieldIndex_eq_padFields (hab e) _ i

/-- The entry algorithm for an entire local map, including demand padding.
A failed check returns `none`; success returns the ordered parameter names. -/
def describe {D : Type*} (src dst : D → J) (a b : D → ℕ) (G : Supply J E) (w : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (table : List S) (code : S ↪ Word bits) (v : E → ℕ)
    (j : J) (d : DemandBits src dst b j) (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) :
    Option (List V) :=
  labels lookup j (indices G w table code v j (fun i => demandFields src dst a i j d) x)

/-- Specializing the output monomial gives exactly the paper's grouped
local entry in every coefficient semiring. -/
theorem describe_correct {D R : Type*} [CommMonoidWithZero R] (src dst : D → J) {a b : D → ℕ}
    (hab : ∀ e, b e ≤ u * a e) (G : Supply J E) (w : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (κ : V → R) (table : List S)
    (complete : ∀ s, s ∈ table) (code : S ↪ Word bits) (v : E → ℕ) (j : J)
    (d : MotifDemandPadding.HalfBits src dst b j) (x : Half G (fun e => Word (v e + u * bits)) j) :
    (describe src dst a b G w lookup table code v j (demandBits src dst j d)
      (mapHalf G (fun _ => inputBits) x)).elim 0 (fun names => (names.map κ).prod) =
      groupedMap G w (fun s j c y => κ (lookup s j c y)) code v j
        (fun i => MotifDemandPadding.demandChunk src dst hab i j d) x := by
  unfold describe groupedMap
  rw [eval_labels, indices_eq_groupedIndices G w table complete]
  simp_rw [demandFields_eq src dst hab]

omit [DecidableEq J] [Fintype E] in
/-- Every successful description denotes a single integral monomial of
total degree at most the number of copies. -/
theorem labels_monomial {G : Supply J E} {w : S → E → ℕ}
    (lookup : ∀ s j, C j → Half G (fun e => Word (w s e)) j → V) (j : J)
    (out : Option (EntryIndices G C w u j)) {names : List V}
    (h : labels lookup j out = some names) :
    ∃ m : V →₀ ℕ, (names.map (MvPolynomial.X (R := ℤ))).prod = MvPolynomial.monomial m 1 ∧
      (names.map (MvPolynomial.X (R := ℤ))).prod.totalDegree ≤ u := by
  cases out with
  | none => simp [labels] at h
  | some t =>
    simp only [labels, Option.map_some, Option.some.injEq] at h
    subst names
    simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]
    exact ⟨_, MotifParameters.prod_entries_eq_monomial _, MotifParameters.prod_entries_degree_le _⟩

section Work

/-- Walk through the copies in order. A cons iteration charges the index step
and the result-list cons in addition to the computed entry's own work. -/
def scanCopies {A : Type*} : {u : ℕ} → (Fin u → A × ℕ) → List A × ℕ
  | 0, _ => ([], 1)
  | _ + 1, f =>
    let head := f 0
    let tail := scanCopies (fun i => f i.succ)
    (head.1 :: tail.1, head.2 + tail.2 + 2)

theorem scanCopies_spec {A : Type*} {u : ℕ} (f : Fin u → A × ℕ) :
    (scanCopies f).1 = List.ofFn (fun i => (f i).1) ∧
      (scanCopies f).2 = (∑ i, (f i).2) + 2 * u + 1 := by
  induction u with
  | zero => simp [scanCopies]
  | succ u ih =>
    obtain ⟨ho, hw⟩ := ih (fun i => f i.succ)
    simp only [scanCopies, List.ofFn_succ, ho, hw, Fin.sum_univ_succ, Nat.mul_succ]
    constructor
    · trivial
    · omega

theorem scanCopies_le {A : Type*} {u B : ℕ} (f : Fin u → A × ℕ) (h : ∀ i, (f i).2 ≤ B) :
    (scanCopies f).2 ≤ (B + 2) * u + 1 := by
  rw [(scanCopies_spec f).2, Nat.add_mul]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => h i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [Nat.mul_comm B u]
  change (∑ i, (f i).2) ≤ u * B at hs
  omega

/-- Scan prior selector entries to find one payload offset. A width read and
addition are charged at each iteration along with the index increment. -/
def widthPrefix : {n : ℕ} → (Fin n → ℕ) → ℕ × ℕ
  | 0, _ => (0, 1)
  | _ + 1, w =>
    let tail := widthPrefix (fun i => w i.succ)
    (w 0 + tail.1, 3 + tail.2)

theorem widthPrefix_spec {n : ℕ} (w : Fin n → ℕ) :
    widthPrefix w = (∑ i, w i, 3 * n + 1) := by
  induction n with
  | zero => simp [widthPrefix]
  | succ n ih =>
    simp only [widthPrefix, ih, Fin.sum_univ_succ, Nat.mul_succ, Prod.mk.injEq, true_and]
    omega

/-- Count the code-table comparisons until the first match. -/
def tableLookup {S : Type*} (p : S → Bool) : List S → Option S × ℕ
  | [] => (none, 1)
  | s :: ss =>
    if p s then (some s, 2) else
      let rest := tableLookup p ss
      (rest.1, 2 + rest.2)

theorem tableLookup_spec {S : Type*} (p : S → Bool) (ss : List S) :
    (tableLookup p ss).1 = ss.find? p ∧ (tableLookup p ss).2 ≤ 2 * ss.length + 1 := by
  induction ss with
  | nil => simp [tableLookup]
  | cons s ss ih =>
    cases hs : p s <;>
      simp only [tableLookup, hs, Bool.false_eq_true, ↓reduceIte, List.find?_cons,
        List.length_cons, ih.1, true_and, Nat.mul_succ]
    all_goals omega

/-- A metered, typed field read. The counter uses indexed bit probes and
word operations on positions, loop counters, and fixed-width base fields. -/
def meteredIndex {n : ℕ} (x : Fin n → Bool) (off k : ℕ) : Word k × ℕ :=
  let t := meteredField x off k
  (⟨t.1, by rw [show t.1 = readField x off k from congrArg Prod.fst (meteredField_spec x off k)]
            exact readField_lt _ _ _⟩, t.2)

theorem meteredIndex_spec {n : ℕ} (x : Fin n → Bool) (off k : ℕ) :
    meteredIndex x off k = (fieldIndex x off k, 6*k+1) := by
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst (meteredField_spec _ _ _))
  · change (meteredField x off k).2 = 6*k+1
    rw [meteredField_spec]

/-- Build a random-access array once. Count the indexed writes and the
iterations of the construction loop, besides each cell's own operations. -/
def arrayRun {A : Type*} {n : ℕ} (f : Fin n → A × ℕ) : (Fin n → A) × ℕ :=
  let a := Vector.ofFn f
  (fun i => a[i.val].1, (∑ i : Fin n, a[i.val].2) + 2*n+1)

theorem arrayRun_spec {A : Type*} {n : ℕ} (f : Fin n → A × ℕ) :
    arrayRun f = (fun i => (f i).1, (∑ i, (f i).2) + 2*n+1) := by simp [arrayRun]

private theorem sum_le_card {I : Type*} [Fintype I] {B : ℕ} (f : I → ℕ) (h : ∀ i, f i ≤ B) :
    ∑ i, f i ≤ Fintype.card I * B := by
  simpa using Finset.sum_le_sum (s := Finset.univ) fun i _ => h i

/-- Scan both ends of the fixed edge list. Each incident port supplies its
input to the given field operation. Charge the loop, the endpoint tests, and
writing the results to the party's local table. -/
def portRun {I : Type*} [Fintype I] (src dst : I → J) {A B : I → Type*} (j : J)
    (f : ∀ e, A e → B e × ℕ)
    (x : ((e : I) → j = src e → A e) × ((e : I) → j = dst e → A e)) :
    (((e : I) → j = src e → B e) × ((e : I) → j = dst e → B e)) × ℕ :=
  ((fun e h => (f e (x.1 e h)).1, fun e h => (f e (x.2 e h)).1),
    ∑ e, ((if h : j = src e then (f e (x.1 e h)).2 else 0) +
          (if h : j = dst e then (f e (x.2 e h)).2 else 0) + 5))

omit [Fintype E] in
theorem portRun_le {I : Type*} [Fintype I] (src dst : I → J) {A B : I → Type*} (j : J)
    (f : ∀ e, A e → B e × ℕ)
    (x : ((e : I) → j = src e → A e) × ((e : I) → j = dst e → A e)) {n : ℕ}
    (h : ∀ e y, (f e y).2 ≤ n) : (portRun src dst j f x).2 ≤ Fintype.card I * (2*n+5) := by
  apply sum_le_card
  intro e
  split <;> split <;> grind

/-- Stage one stores the selector words on all local ports, checks their
agreement, and decodes the anchor's words into a random-access array. -/
def selectorRun (G : Supply J E) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J) (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) :
    Option (Fin u → S) × ℕ :=
  let batches := arrayRun fun i : Fin u => portRun G.src G.dst j (fun e y =>
    let t := meteredIndex y (v e + bits*i.val) bits
    (t.1, t.2+2)) x
  let ports : Half G (fun _ => Fin u → Word bits) j :=
    (fun e he i => (batches.1 i).1 e he, fun e he i => (batches.1 i).2 e he)
  let t := anchor G j ports
  let a := arrayRun fun i =>
    let tag := t i
    tableLookup (fun s => decide (code s = tag)) table
  let decoded := if h : ∀ i : Fin u, (a.1 i).isSome then some fun i => (a.1 i).get (h i) else none
  (if consistent G j ports then decoded else none,
    batches.2 + 2*Fintype.card E*(3*u+3) + a.2 + 3*u+2)

theorem selectorRun_value (G : Supply J E) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J) (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) :
    (selectorRun G table code v j x).1 =
      let tags := mapHalf G (fun _ => readTag) x
      if consistent G j tags then selectors? table code (anchor G j tags) else none := by
  simp only [selectorRun, portRun, arrayRun_spec, meteredIndex_spec, mapHalf,
    (tableLookup_spec _ _).1, selectors?, decode, Vector.getElem_ofFn]
  rfl

private theorem selectorRun_le (G : Supply J E) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J) (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) :
    (selectorRun G table code v j x).2 ≤
      (Fintype.card E*(12*bits+25) + 2*table.length+10)*(u+1) := by
  let f (i : Fin u) (e : E) (y : Fin (v e + u * bits) → Bool) :=
    let t := meteredIndex y (v e + bits*i.val) bits
    (t.1,t.2+2)
  let batch (i : Fin u) := portRun G.src G.dst j (f i) x
  have hf (i : Fin u) (e : E) (y : Fin (v e + u * bits) → Bool) : (f i e y).2 ≤ 6*bits+3 := by
    simp only [f, meteredIndex_spec]
    omega
  have hp := sum_le_card (fun i => (batch i).2) (fun i => portRun_le G.src G.dst j (f i) x (hf i))
  let a := (arrayRun batch).1
  let t := anchor G j (I := fun _ => Fin u → Word bits)
    (fun e h i => (a i).1 e h, fun e h i => (a i).2 e h)
  let g (i : Fin u) := tableLookup (fun s => decide (code s = t i)) table
  have hg := sum_le_card (fun i => (g i).2) (fun i => (tableLookup_spec _ table).2)
  rw [Fintype.card_fin] at hg hp
  change (arrayRun batch).2 + _ + (arrayRun g).2 + _ + 2 ≤ _
  rw [arrayRun_spec, arrayRun_spec]
  dsimp only
  calc
    _ ≤ (u*(Fintype.card E * (2*(6*bits+3)+5))+2*u+1) + 2*Fintype.card E*(3*u+3) +
      (u*(2*table.length+1)+2*u+1)+3*u+2 := by omega
    _ ≤ _ := by
      ring_nf
      omega

/-- Compute and compare every edge's total width, including edges not
incident to the party. -/
def totalRun (w : S → E → ℕ) (v : E → ℕ) (θ : Fin u → S) : Bool × ℕ :=
  let totals := fun e => widthPrefix (fun i => w (θ i) e)
  (decide (∀ e, v e = (totals e).1), ∑ e, ((totals e).2+3))

omit [DecidableEq J] in
theorem totalRun_spec (w : S → E → ℕ) (v : E → ℕ) (θ : Fin u → S) :
    totalRun w v θ = (decide (∀ e, v e = totalWidth w θ e), Fintype.card E*(3*u+4)) := by
  simp [totalRun, widthPrefix_spec, totalWidth]
  rfl

/-- Once the selector array is known, collect both sets of incident fields
for one base copy and return the corresponding parameter-table entry. -/
def nameRun {D : Type*} [Fintype D] (src dst : D → J) (a b : D → ℕ)
    (G : Supply J E) (w : S → E → ℕ) (θ : Fin u → S) (i : Fin u)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (v : E → ℕ) (j : J)
    (d : DemandBits src dst b j) (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) : V × ℕ :=
  let ds := portRun src dst j (fun e y => meteredIndex y (a e * i.val) (a e)) d
  let ps := portRun G.src G.dst j (fun e y =>
    let off := widthPrefix (fun t : Fin i.val => w (θ (Fin.castLE i.isLt.le t)) e)
    let field := meteredIndex (payloadBits y) off.1 (w (θ i) e)
    (field.1, off.2 + field.2 + 2)) x
  (lookup (θ i) j ds.1 ps.1, ds.2 + ps.2 + 3)

private theorem nameRun_value {D : Type*} [Fintype D] (src dst : D → J) (a b : D → ℕ)
    (G : Supply J E) (w : S → E → ℕ) (θ : Fin u → S) (i : Fin u)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (v : E → ℕ) (j : J)
    (d : DemandBits src dst b j) (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) :
    (nameRun src dst a b G w θ i lookup v j d x).1 =
      lookup (θ i) j (demandFields src dst a i j d)
        (mapHalf G (fun e y => fieldIndex (payloadBits y) (offset (fun l => w (θ l) e) i)
          (w (θ i) e)) x) := by
  simp only [nameRun, portRun, meteredIndex_spec, widthPrefix_spec, demandFields, mapHalf, offset]

private theorem nameRun_le {D : Type*} [Fintype D] (src dst : D → J) (a b : D → ℕ)
    (G : Supply J E) (w : S → E → ℕ) (θ : Fin u → S) (i : Fin u)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (v : E → ℕ) (j : J)
    (d : DemandBits src dst b j) (x : Half G (fun e => Fin (v e + u * bits) → Bool) j)
    {A W : ℕ} (ha : ∀ e, a e ≤ A) (hw : ∀ s e, w s e ≤ W) :
    (nameRun src dst a b G w θ i lookup v j d x).2 ≤
      Fintype.card D*(12*A+7) + Fintype.card E*(6*u+12*W+13)+3 := by
  let fd (e : D) (y : Fin (b e) → Bool) := meteredIndex y (a e * i.val) (a e)
  have hd := portRun_le src dst j fd d (n := 6*A+1) (fun e y => by
    simp only [fd, meteredIndex_spec]; have := ha e; omega)
  let fs (e : E) (y : Fin (v e + u * bits) → Bool) :=
    let off := widthPrefix (fun t : Fin i.val => w (θ (Fin.castLE i.isLt.le t)) e)
    let field := meteredIndex (payloadBits y) off.1 (w (θ i) e)
    (field.1, off.2 + field.2 + 2)
  have hs := portRun_le G.src G.dst j fs x (n := 3*u+6*W+4) (fun e y => by
    simp only [fs, widthPrefix_spec, meteredIndex_spec]; have := hw (θ i) e; have := i.isLt; omega)
  change (portRun src dst j fd d).2 + (portRun G.src G.dst j fs x).2 + 3 ≤ _
  convert Nat.add_le_add_right (Nat.add_le_add hd hs) 3 using 1
  ring

/-- Run the three stages on any input, including malformed selectors.
The operation count includes the parameter lookup and each output-list cons. -/
def run {D : Type*} [Fintype D] (src dst : D → J) (a b : D → ℕ)
    (G : Supply J E) (w : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J) (d : DemandBits src dst b j)
    (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) : Option (List V) × ℕ :=
  let sel := selectorRun G table code v j x
  match sel.1 with
  | none => (none, sel.2+1)
  | some θ =>
    let total := totalRun w v θ
    if total.1 then
      let out := scanCopies (fun i => nameRun src dst a b G w θ i lookup v j d x)
      (some out.1, sel.2+total.2+out.2+2)
    else (none, sel.2+total.2+2)

theorem run_value {D : Type*} [Fintype D] (src dst : D → J) (a b : D → ℕ)
    (G : Supply J E) (w : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J) (d : DemandBits src dst b j)
    (x : Half G (fun e => Fin (v e + u * bits) → Bool) j) :
    (run src dst a b G w lookup table code v j d x).1 =
      describe src dst a b G w lookup table code v j d x := by
  unfold run describe labels indices
  dsimp only
  rw [selectorRun_value]
  let tags := mapHalf G (fun _ => readTag) x
  by_cases hag : consistent G j tags = true
  · simp only [tags] at hag
    simp only [hag, ite_true]
    cases selectors? table code _ with
    | none => rfl
    | some θ =>
      dsimp only
      rw [totalRun_spec]
      simp only [decide_eq_true_eq, Option.bind_some, extract]
      split
      · simp only [Option.map_some, (scanCopies_spec _).1, nameRun_value, mapHalf]
      · rfl
  · simp only [tags] at hag
    simp [hag]

/-- The bit-probe and word-operation bound has an absolute quadratic
exponent. Only the fixed motif tables enter the multiplicative constant. -/
theorem run_le {D : Type*} [Fintype D] (src dst : D → J) (a b : D → ℕ)
    (G : Supply J E) (w : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J) (d : DemandBits src dst b j)
    (x : Half G (fun e => Fin (v e + u * bits) → Bool) j)
    {A W : ℕ} (ha : ∀ e, a e ≤ A) (hw : ∀ s e, w s e ≤ W) :
    (run src dst a b G w lookup table code v j d x).2 ≤
      (Fintype.card E*(12*bits+12*W+48) + Fintype.card D*(12*A+7) +
        2*table.length+18) * (u+1)^2 := by
  have hsel := selectorRun_le G table code v j x
  unfold run
  dsimp only
  split
  · apply (Nat.add_le_add_right hsel 1).trans
    ring_nf; omega
  · rename_i θ _
    rw [totalRun_spec]
    split
    · have hnames := scanCopies_le (fun i => nameRun src dst a b G w θ i lookup v j d x)
        (fun i => nameRun_le src dst a b G w θ i lookup v j d x ha hw)
      apply (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hsel _) hnames) 2).trans
      ring_nf; omega
    · apply (Nat.add_le_add_right (Nat.add_le_add_right hsel _) 2).trans
      ring_nf; omega

/-- Read one position by starting at the left end of a stored bit list.
Out-of-range positions return zero. Every advance pays for inspecting the
cell, decrementing the address, and moving to the next cell. -/
def tapeProbe : List Bool → ℕ → Bool × ℕ
  | [], _ => (false, 1)
  | b :: _, 0 => (b, 2)
  | _ :: bs, i+1 =>
    let r := tapeProbe bs i
    (r.1, r.2+3)

theorem tapeProbe_spec (bs : List Bool) (i : ℕ) :
    (tapeProbe bs i).1 = bs[i]?.getD false ∧ (tapeProbe bs i).2 ≤ 3*bs.length+2 := by
  induction bs generalizing i with
  | nil => simp [tapeProbe]
  | cons b bs ih =>
    cases i with
    | zero => simp [tapeProbe]
    | succ i =>
      simp only [tapeProbe, List.getElem?_cons_succ, (ih i).1, true_and, List.length_cons]
      have := (ih i).2
      omega

/-- Sequential storage for one input string of the specified width. -/
abbrev Tape (n : ℕ) := {l : List Bool // l.length = n}

/-- Read the bit at finite index `i` in a motif tape whose length is known. -/
def Tape.readBits {n : ℕ} (t : Tape n) (i : Fin n) : Bool := (tapeProbe t.val i.val).1

/-- Construct a motif tape by listing the bits of a function on `Fin n` in index order. -/
def Tape.ofBits {n : ℕ} (b : Fin n → Bool) : Tape n := ⟨List.ofFn b, List.length_ofFn⟩

theorem Tape.bits_ofBits {n : ℕ} (b : Fin n → Bool) : Tape.readBits (Tape.ofBits b) = b := by
  funext i
  simp [Tape.readBits, Tape.ofBits, (tapeProbe_spec _ _).1, i.isLt]

theorem Tape.probe_le {n : ℕ} (t : Tape n) (i : ℕ) :
    (tapeProbe t.val i).2 ≤ 3*n+2 := by simpa [t.property] using (tapeProbe_spec t.val i).2

/-- A sequential-tape implementation with a conservative allowance for every
indexed probe. The input length is the sum of the fixed motif's edge-string
lengths. Ordinary control and word operations are charged the same allowance. -/
def tapeRun {D : Type*} [Fintype D] (src dst : D → J) (a b : D → ℕ)
    (G : Supply J E) (w : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J)
    (d : ((e : D) → j = src e → Tape (b e)) × ((e : D) → j = dst e → Tape (b e)))
    (x : Half G (fun e => Tape (v e + u * bits)) j) : Option (List V) × ℕ :=
  let result := run src dst a b G w lookup table code v j
    (fun e h => Tape.readBits (d.1 e h), fun e h => Tape.readBits (d.2 e h))
    (mapHalf G (fun _ => Tape.readBits) x)
  let length := (∑ e, b e) + ∑ e, (v e + u*bits)
  (result.1, (3*length+2)*result.2)

/-- Each demand or supply probe in `tapeRun` fits in its reserved allowance. -/
theorem tapeAllowance {D : Type*} [Fintype D] (b : D → ℕ) (v : E → ℕ) (u bits : ℕ) :
    let L := (∑ e, b e) + ∑ e, (v e + u*bits)
    (∀ (e : D) (t : Tape (b e)) i, (tapeProbe t.val i).2 ≤ 3*L+2) ∧
    (∀ (e : E) (t : Tape (v e+u*bits)) i, (tapeProbe t.val i).2 ≤ 3*L+2) := by
  constructor
  · intro e t i
    have h := Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    have ht := t.probe_le i
    omega
  · intro e t i
    have h := Finset.single_le_sum (f := fun e => v e+u*bits)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    have ht := t.probe_le i
    omega

/-- The rescan implementation has an absolute polynomial exponent even when
the input tapes contain malformed data. -/
theorem tapeRun_le {D : Type*} [Fintype D] (src dst : D → J) (a b : D → ℕ)
    (G : Supply J E) (w : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e => Word (w s e)) j → V) (table : List S) (code : S ↪ Word bits)
    (v : E → ℕ) (j : J)
    (d : ((e : D) → j = src e → Tape (b e)) × ((e : D) → j = dst e → Tape (b e)))
    (x : Half G (fun e => Tape (v e + u * bits)) j)
    {A W : ℕ} (ha : ∀ e, a e ≤ A) (hw : ∀ s e, w s e ≤ W) :
    let L := (∑ e, b e) + ∑ e, (v e + u*bits)
    (tapeRun src dst a b G w lookup table code v j d x).2 ≤
      (3*L+2) * ((Fintype.card E*(12*bits+12*W+48) + Fintype.card D*(12*A+7) +
        2*table.length+18)*(u+1)^2) :=
  Nat.mul_le_mul_left _ (run_le src dst a b G w lookup table code v j _ _ ha hw)

end Work

end MotifEntry

end VPVNP
end Computability
end OAI

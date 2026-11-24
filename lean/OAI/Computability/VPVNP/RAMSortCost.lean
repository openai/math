import OAI.Computability.VPVNP.RAMSortCostLayout
import OAI.Computability.VPVNP.RAMSortCompareCost
import OAI.Computability.VPVNP.RAMSortDecodeCost
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Word work of the local bitonic validator

A site materializes its next block in a second array, scanning every local
offset once per layer. At a cross-site stride it reads both five-word fields
from the site's incident bit array. It validates both encodings, checks the
send against the current record, and uses the receive in the comparator.
Malformed fields set a failure flag. All loop lengths are public, including
on paths that have already set this flag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

open BurstRAM RAMSerialization RAMMemory

variable {h d w : ℕ}

private abbrev Slot (w : ℕ) := OrderedSlot (Word w)

private def orderedRecord (r : Option (WordRecord w)) : Slot w := ⟨r.map WordRecord.record⟩

/-- Parse one record at its exact linear address in the incident bit array.
In addition to the word scan, each of its `5*w` reads adds the record's base
to the within-record bit index. -/
def readSlot (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d)) (dir : Fin 2)
    (i : Fin (2 ^ h)) : Option (OrderedSlot (Word w)) × ℕ :=
  let start := fieldStart h w s.phase s.stride dir.val i.val
  let decoded := decodeSlot hw (fun bit ↦ incident (start.eval + bit.val))
  (decoded.1.map orderedRecord, start.work + 5*w + decoded.2)

theorem readSlot_cost (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d)) (dir : Fin 2)
    (i : Fin (2 ^ h)) : (readSlot hw incident s dir i).2 ≤ 21 + 5*w + 64*(w+1) := by
  unfold readSlot
  simp only [fieldStart_work]
  exact Nat.add_le_add_left (decodeSlot_cost ..) _

private def emptySlot : Slot w := ⟨none⟩

private def exchange (keepMin : Bool) (x y : Slot w) : Slot w × ℕ :=
  let cmp := compareSlots x y
  -- One Boolean equality, a branch and five word copies.
  (if cmp.1 == keepMin then x else y, cmp.2 + 7)

private theorem exchange_value (keepMin : Bool) (x y : Slot w) :
    (exchange keepMin x y).1 = if keepMin then min x y else max x y := by
  by_cases hle : x ≤ y
  · cases keepMin <;> simp [exchange, compareSlots_result, hle]
  · have hy := le_of_not_ge hle
    cases keepMin <;> simp [exchange, compareSlots_result, hle, min_eq_right hy, max_eq_left hy]

/-- Result of processing one wire offset in a local sorting layer, with its selected record,
validation flag, and work charge. -/
structure SiteRow (w : ℕ) where
  /-- Padded record selected by the comparator for this wire in the next layer. -/
  slot : OrderedSlot (Word w)
  /-- Per-offset validation flag. At a cross-site layer it checks both encodings and agreement
  of the outgoing record with the current wire. -/
  ok : Bool
  /-- Word operations charged to addressing, reading, checking, and comparing the records at
  this offset. -/
  steps : ℕ

/-- One bounded per-offset operation. Local strides have no incident fields.
The additional constant steps cover tag-presence checks, Boolean operations,
five output writes and offset-loop control. -/
def scanRow (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d)) (v : Fin (2^d))
    (current : Wires h (Slot w)) (i : Fin (2^h)) : SiteRow w :=
  let g := wireIndex h v.val i.val
  let p := wirePartner h v.val i.val s.stride
  let dir := directionBit h v.val i.val s.phase
  let keepMin := decide (g.eval < p.eval) == decide (dir.eval = 0)
  let addressWork := g.work + p.work + dir.work + 2
  if hc : h ≤ s.stride then
    let out := readSlot hw incident s 0 i
    let inc := readSlot hw incident s 1 i
    let sent := out.1.getD emptySlot
    let ab := compareSlots sent (current i)
    let ba := compareSlots (current i) sent
    let next := exchange keepMin (current i) (inc.1.getD emptySlot)
    ⟨next.1, out.1.isSome && inc.1.isSome && ab.1 && ba.1,
      addressWork + out.2 + inc.2 + ab.2 + ba.2 + next.2 + 20⟩
  else
    let other := current ⟨partner s.stride i, partner_lt i.isLt (Nat.lt_of_not_ge hc)⟩
    let next := exchange keepMin (current i) other
    -- Shift/xor for the local partner, plus writes and loop control.
    ⟨next.1, true, addressWork + next.2 + 12⟩

/-- What the local send and receive field parsers return for this layer.
The receive field comes from the unique designated partner. -/
def Loads (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d)) (send : Sends h d s (Slot w))
    (v : Fin (2^d)) : Prop :=
  ∀ hc : h ≤ s.stride, ∀ i,
    (readSlot hw incident s 0 i).1 = some (send hc v i) ∧
    (readSlot hw incident s 1 i).1 = some (send hc (sourceSite s hc v) i)

private theorem exchange_orientation (first up : Bool) (x y : Slot w) :
    (exchange (first == up) x y).1 = if first then lower up x y else upper up y x := by
  rw [exchange_value]
  cases first <;> cases up <;> simp [lower, upper, min_comm, max_comm]

private theorem scanRow_spec (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d))
    (send : Sends h d s (Slot w)) (v : Fin (2^d)) (current : Wires h (Slot w))
    (i : Fin (2^h)) (hs : Loads hw incident s send v) :
    (scanRow hw incident s v current i).slot = localLayer s send v current i ∧
      ((scanRow hw incident s v current i).ok = true ↔ ∀ hc, send hc v i = current i) := by
  by_cases hc : h ≤ s.stride
  · obtain ⟨h₀, h₁⟩ := hs hc i
    simp only [scanRow, localLayer, hc, dite_true, h₀, h₁, Option.getD_some, Option.isSome_some,
      wireIndex_eval, wirePartner_eval, directionBit_eval, exchange_orientation, compareSlots_result,
      Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    simp only [true_and]
    exact ⟨fun h _ ↦ le_antisymm h.1 h.2, fun he ↦ ⟨(he trivial).le, (he trivial).ge⟩⟩
  · simp [scanRow, localLayer, hc, exchange_orientation]

/-- Output array, status flag and work accumulated during a materialized
scan of one site block or of several consecutive layers. -/
structure Scan (h w : ℕ) where
  /-- The site’s array of padded records after the scanned sorting layers. -/
  block : Wires h (Slot w)
  /-- Conjunction of the per-offset validation flags over the layers processed by the scan. -/
  ok : Bool
  /-- Accumulated word work of the site’s scan, including the row charges and public loop
  overhead. -/
  steps : ℕ

/-- Tabulate all offsets into the next buffer, retaining the conjunction of
their flags. Each row is computed once. The two buffers can swap roles. -/
def scanLayer (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d))
    (v : Fin (2^d)) (current : Wires h (Slot w)) : Scan h w :=
  let rows := Vector.ofFn (scanRow hw incident s v current)
  ⟨fun i ↦ rows[i.val].slot, (List.ofFn (fun i : Fin (2^h) ↦ rows[i.val].ok)).all id,
    (∑ i : Fin (2^h), rows[i.val].steps) + 4⟩

/-- Public phase and stride loops. Rejection is latched, so the upper bound
also covers arbitrary messages after the first failing check. -/
def scanStages (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d)) :
    List (Stage (h+d)) → Wires h (Slot w) → Scan h w
  | [], current => ⟨current, true, 1⟩
  | s :: ss, current =>
    let step := scanLayer hw incident s v current
    let rest := scanStages hw incident v ss step.block
    ⟨rest.block, step.ok && rest.ok, step.steps + rest.steps + 5⟩

/-- Successful raw parsing of all chronological send/receive fields into
the corresponding records of a replay assignment. -/
def LoadsStages (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d)) :
    (ss : List (Stage (h+d))) → Fields h d (Slot w) ss → Prop
  | [], _ => True
  | s :: ss, fields => Loads hw incident s fields.1 v ∧ LoadsStages hw incident v ss fields.2

/-- Whenever the physical fields parse, this costed scan runs exactly the
local validator: it gives the same resulting records and the same decision. -/
theorem scanStages_spec (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d))
    (ss : List (Stage (h+d))) (fields : Fields h d (Slot w) ss) (current : Wires h (Slot w))
    (hs : LoadsStages hw incident v ss fields) :
    (scanStages hw incident v ss current).block = replay v ss fields current ∧
      ((scanStages hw incident v ss current).ok = true ↔ checks v ss fields current) := by
  induction ss generalizing current with
  | nil => simp [scanStages, replay, checks]
  | cons s ss ih =>
    have hr := fun i ↦ scanRow_spec hw incident s fields.1 v current i hs.1
    have hblock : (scanLayer hw incident s v current).block = localLayer s fields.1 v current :=
      funext fun i ↦ by simpa [scanLayer] using (hr i).1
    have hok : (scanLayer hw incident s v current).ok = true ↔ ∀ hc, fields.1 hc v = current := by
      simp only [scanLayer, Vector.getElem_ofFn, List.all_eq_true, List.mem_ofFn, id_eq]
      constructor
      · intro hh hc
        funext i
        exact ((hr i).2.mp (hh _ ⟨i, rfl⟩)) hc
      · rintro hh _ ⟨i, rfl⟩
        exact (hr i).2.mpr fun hc ↦ congrFun (hh hc) i
    have ht := ih fields.2 (localLayer s fields.1 v current) hs.2
    simp only [scanStages, replay, checks, hblock, Bool.and_eq_true, hok, ht.1, ht.2, true_and]

private theorem canonical_of_readSlot (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d))
    (dir : Fin 2) (i : Fin (2 ^ h)) (hp : (readSlot hw incident s dir i).1.isSome = true) :
    ∃ r : Option (WordRecord w),
      (fun bit : Fin (5*w) ↦ incident ((fieldStart h w s.phase s.stride dir.val i.val).eval +
        bit.val)) = (recordFormat hw).encode r := by
  let bits := fun bit : Fin (5*w) ↦
    incident ((fieldStart h w s.phase s.stride dir.val i.val).eval + bit.val)
  change ((decodeSlot hw bits).1.map orderedRecord).isSome = true at hp
  rw [decodeSlot_eq] at hp
  cases hp' : (recordFormat hw).decode bits with
  | none => simp [hp'] at hp
  | some r => exact ⟨r, ((recordFormat hw).decode_iff bits r).mp hp'⟩

/-- Passing the costed scan forces every raw send and receive field used by
this site to be a canonical encoding. A malformed tag or noncanonical
padding at any layer prevents acceptance. -/
theorem scanStages_canonical (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d))
    (ss : List (Stage (h+d))) (current : Wires h (Slot w))
    (hp : (scanStages hw incident v ss current).ok = true) :
    ∀ s ∈ ss, h ≤ s.stride → ∀ dir : Fin 2, ∀ i : Fin (2^h), ∃ r : Option (WordRecord w),
      (fun bit : Fin (5*w) ↦ incident ((fieldStart h w s.phase s.stride dir.val i.val).eval +
        bit.val)) = (recordFormat hw).encode r := by
  induction ss generalizing current with
  | nil => simp
  | cons s ss ih =>
    obtain ⟨hfirst, htail⟩ := Bool.and_eq_true_iff.mp hp
    intro t ht hc dir i
    rcases List.mem_cons.mp ht with rfl | hmem
    · have hr : (scanRow hw incident t v current i).ok = true := by
        simp only [scanLayer, Vector.getElem_ofFn] at hfirst
        exact List.all_eq_true.mp hfirst _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      simp only [scanRow, hc, dite_true, Bool.and_eq_true] at hr
      apply canonical_of_readSlot
      have hdir : dir = 0 ∨ dir = 1 := by
        have hv : dir.val = 0 ∨ dir.val = 1 := by have := dir.isLt; omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hdir with rfl | rfl
      · exact hr.1.1.1
      · exact hr.1.1.2
    · exact ih _ htail t hmem hc dir i

/-- Work bound for one offset, including two arbitrary five-word fields on
a cross-site layer. -/
theorem scanRow_cost (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d)) (v : Fin (2^d))
    (current : Wires h (Slot w)) (i : Fin (2^h)) :
    (scanRow hw incident s v current i).steps ≤ 1000 * (w+1) := by
  by_cases hc : h ≤ s.stride
  · have ho := readSlot_cost hw incident s 0 i
    have hi := readSlot_cost hw incident s 1 i
    simp only [scanRow, hc, dite_true, wireAddress_work, exchange, compareSlots_steps]
    omega
  · simp only [scanRow, hc, dite_false, wireAddress_work, exchange, compareSlots_steps]
    omega

theorem scanStages_cost (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d))
    (ss : List (Stage (h+d))) (current : Wires h (Slot w)) :
    (scanStages hw incident v ss current).steps ≤ 1 + ss.length * (2^h * (1000*(w+1)) + 9) := by
  induction ss generalizing current with
  | nil => simp [scanStages]
  | cons s ss ih =>
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ scanRow_cost hw incident s v current i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] at hsum
    have ht := ih (scanLayer hw incident s v current).block
    simp only [scanStages, scanLayer, Vector.getElem_ofFn, List.length_cons, Nat.add_mul,
      Nat.one_mul, Fin.eta] at ht ⊢
    omega

/-- Exact public loop bound. The slot bound applies even when a field
encodes a bad tag or nonzero padding. -/
theorem sortScan_cost (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d))
    (current : Wires h (Slot w)) :
    (scanStages hw incident v (phases (h+d) (h+d) le_rfl) current).steps ≤
      1 + (h+d+1).choose 2 * (2^h * (1000*(w+1)) + 9) := by
  simpa using scanStages_cost hw incident v (phases (h+d) (h+d) le_rfl) current

/-- Emit the `k` stride entries of a phase directly onto a supplied suffix.
Each iteration tests and decrements the counter, writes the two stage words,
and links the new entry. -/
def emitStrides (b a : ℕ) (ha : a ≤ b) :
    (k : ℕ) → k ≤ a → List (Stage b) → List (Stage b) × ℕ
  | 0, _, tail => (tail, 1)
  | k+1, hk, tail =>
    let rest := emitStrides b a ha k (Nat.le_of_succ_le hk) tail
    (⟨a,k,hk,ha⟩ :: rest.1, rest.2 + 5)

private theorem emitStrides_spec (b a : ℕ) (ha : a ≤ b) (k : ℕ) (hk : k ≤ a)
    (tail : List (Stage b)) :
    emitStrides b a ha k hk tail = (strides b a ha k hk ++ tail, 1 + 5*k) := by
  induction k with
  | zero => simp [emitStrides, strides]
  | succ k ih => simp [emitStrides, strides, ih, Nat.mul_add, Nat.add_assoc]

/-- Generate the public chronological layer schedule in a single pass,
using a suffix accumulator. The construction copies each stage only once. -/
def emitPhases (b : ℕ) : (a : ℕ) → a ≤ b → List (Stage b) → List (Stage b) × ℕ
  | 0, _, tail => (tail, 1)
  | a+1, ha, tail =>
    let suffix := emitStrides b (a+1) ha (a+1) le_rfl tail
    let result := emitPhases b a (Nat.le_of_succ_le ha) suffix.1
    (result.1, suffix.2 + result.2 + 4)

/-- Exact word charge for emitting the public phase and stride schedule. -/
theorem emitPhases_spec (b a : ℕ) (ha : a ≤ b) (tail : List (Stage b)) :
    emitPhases b a ha tail = (phases b a ha ++ tail, 1 + 5*a + 5*(a+1).choose 2) := by
  induction a generalizing tail with
  | zero => simp [emitPhases, phases]
  | succ a ih =>
    simp only [emitPhases, emitStrides_spec, ih, phases, List.append_assoc,
      Nat.choose_succ_succ (a+1) 1, Nat.choose_one_right, Nat.reduceSucc, Prod.mk.injEq, true_and]
    omega

/-- Complete costed sorting subroutine, including the linear-time generation
of all comparator layers. -/
def scanSort (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d))
    (current : Wires h (Slot w)) : Scan h w :=
  if h+d = 0 then ⟨current, true, 1⟩
  else
    let stages := emitPhases (h+d) (h+d) le_rfl []
    let run := scanStages hw incident v stages.1 current
    ⟨run.block, run.ok, stages.2 + run.steps + 1⟩

@[simp] theorem scanSort_block (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d))
    (current : Wires h (Slot w)) :
    (scanSort hw incident v current).block =
      (scanStages hw incident v (phases (h+d) (h+d) le_rfl) current).block := by
  by_cases hb : h+d = 0
  · obtain ⟨rfl, rfl⟩ : h = 0 ∧ d = 0 := by omega
    rfl
  · simp only [scanSort, hb, ite_false, emitPhases_spec, List.append_nil]

@[simp] theorem scanSort_ok (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d))
    (current : Wires h (Slot w)) :
    (scanSort hw incident v current).ok =
      (scanStages hw incident v (phases (h+d) (h+d) le_rfl) current).ok := by
  by_cases hb : h+d = 0
  · obtain ⟨rfl, rfl⟩ : h = 0 ∧ d = 0 := by omega
    rfl
  · simp only [scanSort, hb, ite_false, emitPhases_spec, List.append_nil]

private theorem layers_ge_phase (b : ℕ) : b ≤ (b+1).choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.choose_succ_succ (b+1) 1, Nat.choose_one_right]
    exact Nat.le_add_right ..

/-- All parsing, address computations, comparator applications and public
schedule generation in the sorting subroutine have a uniform word bound. -/
theorem scanSort_cost (hw : 2 ≤ w) (incident : ℕ → Bool) (v : Fin (2^d))
    (current : Wires h (Slot w)) :
    (scanSort hw incident v current).steps ≤
      1 + (h+d+1).choose 2 * (2^h * (1024*(w+1)) + 9) := by
  by_cases hb : h+d = 0
  · obtain ⟨rfl, rfl⟩ : h = 0 ∧ d = 0 := by omega
    simp [scanSort]
  · let L := (h+d+1).choose 2
    have hL : h+d ≤ L := layers_ge_phase (h+d)
    have hwork := sortScan_cost hw incident v current
    have hscale : 1 ≤ 2^h * (w+1) := Nat.mul_pos (Nat.two_pow_pos h) (Nat.succ_pos _)
    have hslack : 2^h * (1000*(w+1)) + 9 + 12 ≤ 2^h * (1024*(w+1)) + 9 := by
      rw [Nat.mul_left_comm (2^h) 1000, Nat.mul_left_comm (2^h) 1024]
      omega
    have hmain := Nat.mul_le_mul_left L hslack
    rw [Nat.mul_add L _ 12] at hmain
    simp only [scanSort, hb, ite_false, emitPhases_spec, List.append_nil]
    change _ ≤ 1 + L * (2^h * (1024*(w+1)) + 9)
    change _ ≤ 1 + L * (2^h * (1000*(w+1)) + 9) at hwork
    change 1 + 5*(h+d) + 5*L + _ + 1 ≤ _
    omega

end RAMSort

end VPVNP
end Computability
end OAI

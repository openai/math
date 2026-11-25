import OAI.Computability.BorderVNP.TeamTapeSorting
import OAI.Computability.BorderVNP.TeamSorting

/-! # Per-processor layout of the physical team sorter

Each processor stages its own bounded probe records as successive read/write pairs, then
pads its block with the canonical empty slot. The global input address is the ordinary
row-major index. Extra power-of-two blocks start empty. These definitions identify the
block emitted by the physical buffer with the one consumed by the named-stack post-pass.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeSorting

open VPVNP BurstRAM RAMTape RAMMemory RAMSerialization RAMSort

attribute [local instance] portDecidableEq

variable {w e d : ℕ}

/-- Pack all probes in one local row into their bounded physical read/write slots. -/
def packRow : (rs : List (TeamRecords.Record (Word w))) →
    (∀ r ∈ rs, ProbeFits r) → List (WordRecord w)
  | [], _ => []
  | r :: rs, hf => wordPair r (hf r (by simp)) ++ packRow rs (fun z hz => hf z (List.mem_cons_of_mem _ hz))

/-- Doubling the number of slots accounts for every old-word check, including writes. -/
theorem length_packRow (rs : List (TeamRecords.Record (Word w))) (hf) :
    (packRow rs hf).length = 2*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [packRow, wordPair, ih]; omega

/-- Widening the serialized slots gives the exact chronology-preserving expansion. -/
theorem packRow_decode (rs : List (TeamRecords.Record (Word w))) (hf) :
    (packRow rs hf).map WordRecord.record = rs.flatMap TeamRecords.pair := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [packRow, wordPair_decode, ih]

/-- Row-major packed record array. Missing positions within a block, and addresses past
the last virtual block, have the unique empty slot. -/
def rowInput (e : ℕ) (rows : Word d → List (WordRecord w)) (i : ℕ) : Option (WordRecord w) :=
  if hv : i / 2^(2+e) < 2^d then (rows ⟨i / 2^(2+e), hv⟩)[i % 2^(2+e)]? else none

private theorem rowInput_at (rows : Word d → List (WordRecord w)) (v : Word d)
    (i : Word (2+e)) : block (2+e) v.val (rowInput e rows) i = (rows v)[i.val]? := by
  simp [block, rowInput, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt i.isLt,
    Nat.mul_comm v.val, Nat.mod_eq_of_lt i.isLt, v.isLt]

/-- After closing the local pair buffer the physical post-pass reads its bytes verbatim. -/
theorem rawBlock_eq_emitted (hw : 2 ≤ w) (rows : Word d → List (WordRecord w)) (v : Word d) :
    rawBlock hw e v (rowInput e rows) = SortReplay.emittedBlock hw e (rows v) := by
  funext i
  rw [rawBlock, rowInput_at]
  rfl

private theorem row_occupied (rows : Word d → List (WordRecord w)) (v : Word d)
    (hfit : (rows v).length ≤ 4*2^e) :
    (List.ofFn (block (2+e) v.val (wire (rowInput e rows)))).filterMap OrderedSlot.record =
      (rows v).map WordRecord.record := by
  have eq : block (2+e) v.val (wire (rowInput e rows)) = fun i =>
      OrderedSlot.mk (((RecordBuffer.slots (2^e) (rows v)) (recordPosition e i)).map WordRecord.record) := by
    funext i
    apply congrArg OrderedSlot.mk
    apply congrArg (Option.map WordRecord.record)
    exact rowInput_at rows v i
  rw [eq, List.ofFn_congr (record_width e)]
  have hl : (List.ofFn fun i : Fin (4*2^e) =>
      OrderedSlot.mk (((RecordBuffer.slots (2^e) (rows v)) i).map WordRecord.record)) =
      (List.ofFn (RecordBuffer.slots (2^e) (rows v))).map
        (fun r => OrderedSlot.mk (r.map WordRecord.record)) := by rw [List.map_ofFn]; rfl
  change (List.ofFn fun i : Fin (4*2^e) =>
    OrderedSlot.mk (((RecordBuffer.slots (2^e) (rows v)) i).map WordRecord.record)).filterMap _ = _
  rw [hl, RecordBuffer.slots_list _ _ hfit, List.filterMap_map]
  simp [List.filterMap_append, List.filterMap_map]

/-- Recover every active slot exactly once and erase all padding in the global input. -/
theorem occupied_rowInput (rows : Word d → List (WordRecord w)) (hfit : ∀ v, (rows v).length ≤ 4*2^e) :
    occupied ((2+e)+d) (rowInput e rows) = (List.ofFn rows).flatten.map WordRecord.record := by
  rw [occupied, ← flatten_ofFn_blocks, List.filterMap_flatten, List.map_flatten]
  simp only [List.map_ofFn, Function.comp_def, row_occupied rows _ (hfit _)]

/-- The layout assigns each real processor its own original row and every virtual padding
processor an empty row. -/
def padRows {r : ℕ} {α : Type*} (rows : Fin r → List α) (v : Word (Nat.clog 2 r)) : List α :=
  if hv : v.val < r then rows ⟨v.val, hv⟩ else []

/-- Power-of-two padding adds no occupied records to the chronological concatenation. -/
theorem flatten_padRows {r : ℕ} {α : Type*} (rows : Fin r → List α) :
    (List.ofFn (padRows rows)).flatten = (List.ofFn rows).flatten := by
  let extra := 2 ^ Nat.clog 2 r - r
  have heq : 2 ^ Nat.clog 2 r = r+extra := by have := Nat.le_pow_clog (b := 2) (by decide) r; dsimp [extra]; omega
  rw [List.ofFn_congr heq, List.ofFn_add, List.flatten_append]
  have lhs : (fun i : Fin r => padRows rows (Fin.cast heq.symm (Fin.castAdd extra i))) = rows := by
    funext i; simp [padRows, i.isLt]
  have rhs : (fun i : Fin extra => padRows rows (Fin.cast heq.symm (Fin.natAdd r i))) =
      fun _ => [] := by funext i; simp [padRows]
  have he : ∀ k : ℕ, (List.replicate k ([] : List α)).flatten = [] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  simp only [rhs, List.ofFn_const, he, List.append_nil]
  exact congrArg (fun f : Fin r → List α => (List.ofFn f).flatten) lhs

/-- Per-processor raw memory sort, for any positive number of real processors. No
permutation of packed physical slots is required as a premise. Only the chronology
of the locally emitted probes is compared with the original RAM path. -/
theorem existsUnique_rowBits {r : ℕ} (hw : 2 ≤ w) (hc : 2^(Nat.clog 2 r)*2^e < 2^w)
    (rows : Fin r → List (TeamRecords.Record (Word w))) (hf : ∀ v, ∀ z ∈ rows v, ProbeFits z)
    (hfit : ∀ v, 2*(rows v).length ≤ 4*2^e)
    {es : List (TeamRecords.Access (Word w))} {rs : List (TeamRecords.Record (Word w))}
    (he : TeamRecords.Matches es rs) (ht : TeamRecords.Timed es)
    (hp : rs.Perm (List.ofFn rows).flatten) (t : ℕ) (hclock : siteBudget (Nat.clog 2 r) e w ≤ t) :
    let bytes := rowInput e (padRows (fun v => packRow (rows v) (hf v)))
    (∃! a : Fields (Nat.clog 2 r) e w, ∀ v,
      program.body.count (fun _ _ => 0) t (siteInput hw a v bytes) = 1) ↔
      rs = TeamRecords.transcript (fun _ => 0) es := by
  let packed := fun v => packRow (rows v) (hf v)
  let virtual := padRows packed
  have cap (v) : (virtual v).length ≤ 4*2^e := by
    by_cases hv : v.val < r
    · simpa [virtual, padRows, hv, packed, length_packRow] using hfit ⟨v.val,hv⟩
    · simp [virtual, padRows, hv]
  have hp' : (rs.flatMap TeamRecords.pair).Perm (occupied ((2+e)+Nat.clog 2 r) (rowInput e virtual)) := by
    rw [occupied_rowInput virtual cap, flatten_padRows, List.map_flatten]
    have eq : ((List.ofFn rows).flatten.flatMap TeamRecords.pair) =
        ((List.ofFn packed).map (List.map WordRecord.record)).flatten := by
      simp only [List.flatMap_def, List.map_flatten, List.map_ofFn, Function.comp_def, packed,
        packRow_decode, List.flatten_flatten]
    rw [← eq]
    exact hp.flatMap (fun _ _ => .refl _)
  exact existsUnique_bits_iff_transcript hw hc (rowInput e virtual) he ht hp' t hclock

end TeamTapeSorting

end BorderVNP
end Computability
end OAI

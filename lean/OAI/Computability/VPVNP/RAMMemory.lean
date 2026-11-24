import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot

/-!
# Memory checks in the distributed RAM transcript

In Lemma 10.1, the guessed values of external reads are checked using only the
previous record in address-sorted order. Initialization records are writes.
The chronological semantics below leaves memory unchanged on a read, and
checks the guessed value against the actual current memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMMemory

/-- Memory transcript operation, distinguished as a header initialization, an external read or
an external write. -/
inductive Kind where
  | init | read | write
  deriving DecidableEq

/-- Nonempty five-word records. Padding is represented by `none`. -/
structure Record (Word : Type*) where
  /-- Operation that produced this record, used to give header initialization priority over
  later probes. -/
  kind : Kind
  /-- External address to which this initialization or probe refers. -/
  address : ℕ
  /-- Word installed by an initialization or write, or the value claimed by a read. -/
  value : Word
  /-- Cumulative cost at the start of the issuing call. Initialization records use their own
  address in this timestamp field. -/
  startCost : ℕ
  /-- Probe index within its issuing call, used with the start cost to order probes
  chronologically. -/
  ordinal : ℕ
  deriving DecidableEq

variable {Word : Type*}

/-- Initialization precedes every probe. Probes are ordered by the starting
cost of their call and their ordinal within that call. -/
def Record.timestamp (r : Record Word) : Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (if r.kind = .init then 0 else 1, toLex (r.startCost, r.ordinal))

/-- The order of events in the RAM computation. -/
def Chronological (records : List (Record Word)) : Prop :=
  records.Pairwise fun x y => x.timestamp < y.timestamp

/-- Strict order of the nonempty keys in the sorted probe array. -/
def AddressSorted (records : List (Record Word)) : Prop :=
  records.Pairwise fun x y => x.address < y.address ∨
    x.address = y.address ∧ x.timestamp < y.timestamp

/-- Execute one probe. A read does not modify memory. -/
def afterRecord (mem : ℕ → Word) (r : Record Word) : ℕ → Word :=
  fun a => if r.kind = .read then mem a else Function.update mem r.address r.value a

/-- Correctness of the claimed read values under ordinary sequential RAM
execution from the given memory. Writes may overwrite any previous value. -/
def ReadsCorrect (mem : ℕ → Word) : List (Record Word) → Prop
  | [] => True
  | r :: rs => (r.kind = .read → r.value = mem r.address) ∧
      ReadsCorrect (afterRecord mem r) rs

variable [Zero Word]

/-- Previous value if the previous record addresses this cell, and zero
otherwise. This needs only the predecessor site's last record at a block edge. -/
def previousValue (previous : Option (Record Word)) (address : ℕ) : Word :=
  match previous with
  | none => 0
  | some r => if r.address = address then r.value else 0

/-- The local predecessor test on all reads of one block. -/
def PredecessorCheck (previous : Option (Record Word)) : List (Record Word) → Prop
  | [] => True
  | r :: rs => (r.kind = .read → r.value = previousValue previous r.address) ∧
      PredecessorCheck (some r) rs

private def atAddress (a : ℕ) (records : List (Record Word)) :=
  records.filter fun r => r.address == a

private def cellCheck (v : Word) : List (Record Word) → Prop
  | [] => True
  | r :: rs => (r.kind = .read → r.value = v) ∧
      cellCheck (if r.kind = .read then v else r.value) rs

omit [Zero Word] in
private theorem readsCorrect_iff_cells (mem : ℕ → Word) (records : List (Record Word)) :
    ReadsCorrect mem records ↔ ∀ a, cellCheck (mem a) (atAddress a records) := by
  induction records generalizing mem with
  | nil => simp [ReadsCorrect, atAddress, cellCheck]
  | cons r rs ih =>
    rw [ReadsCorrect, ih]
    have hsame : afterRecord mem r r.address =
        if r.kind = .read then mem r.address else r.value := by
      split <;> simp_all [afterRecord]
    have hother (a : ℕ) (ha : r.address ≠ a) : afterRecord mem r a = mem a := by
      simp [afterRecord, Function.update_of_ne ha.symm]
    constructor
    · rintro ⟨hread, htail⟩ a
      by_cases ha : r.address = a
      · subst a
        simpa [atAddress, cellCheck, hsame] using And.intro hread (htail r.address)
      · simpa [atAddress, ha, hother a ha] using htail a
    · intro hall
      have h := hall r.address
      simp [atAddress, cellCheck] at h
      refine ⟨h.1, fun a => ?_⟩
      by_cases ha : r.address = a
      · subst a
        simpa [hsame, atAddress] using h.2
      · simpa [atAddress, ha, hother a ha] using hall a

omit [Zero Word] in
/-- Sorting groups each address while preserving its complete probe history,
including intermediate reads. Strict timestamps prevent tie ambiguities. -/
private theorem address_histories_eq {chron sorted : List (Record Word)}
    (hp : chron.Perm sorted) (hc : Chronological chron) (hs : AddressSorted sorted) (a : ℕ) :
    atAddress a chron = atAddress a sorted := by
  let p := fun (r : Record Word) => r.address == a
  have hchron := hc.filter p
  have hsorted := hs.filter p
  have htime : (sorted.filter p).Pairwise fun x y => x.timestamp < y.timestamp := by
    apply hsorted.imp_of_mem
    intro x y hx hy hxy
    have hxa : x.address = a := by simpa [p] using (List.mem_filter.mp hx).2
    have hya : y.address = a := by simpa [p] using (List.mem_filter.mp hy).2
    simpa [hxa, hya] using hxy
  exact (hp.filter p).eq_of_pairwise (fun _ _ _ _ hxy hyx => (lt_asymm hxy hyx).elim)
    hchron htime

private theorem predecessorCheck_iff_sorted {previous : Option (Record Word)}
    {mem : ℕ → Word} {sorted : List (Record Word)} (hs : AddressSorted sorted)
    (hp : ∀ p ∈ previous, ∀ r ∈ sorted, p.address ≤ r.address)
    (hm : ∀ r ∈ sorted, mem r.address = previousValue previous r.address) :
    PredecessorCheck previous sorted ↔ ReadsCorrect mem sorted := by
  induction sorted generalizing previous mem with
  | nil => simp [PredecessorCheck, ReadsCorrect]
  | cons r rs ih =>
    obtain ⟨hr, htail⟩ := List.pairwise_cons.mp hs
    have hle (s : Record Word) (hsr : s ∈ rs) : r.address ≤ s.address :=
      (hr s hsr).elim le_of_lt (fun h => h.1.le)
    rw [PredecessorCheck, ReadsCorrect, hm r (List.mem_cons_self ..)]
    apply and_congr_right
    intro hread
    apply ih htail
    · simpa using hle
    · intro s hsr
      by_cases heq : r.address = s.address
      · rw [← heq]
        simp only [previousValue, afterRecord]
        by_cases hk : r.kind = .read
        · simpa [hk, hm r (List.mem_cons_self ..)] using (hread hk).symm
        · simp [hk]
      · have hzero : previousValue previous s.address = 0 := by
          cases previous with
          | none => rfl
          | some p =>
            have hpr := hp p (by simp) r (List.mem_cons_self ..)
            have hps : p.address ≠ s.address :=
              (lt_of_le_of_lt hpr (lt_of_le_of_ne (hle s hsr) heq)).ne
            simp [previousValue, hps]
        simp [afterRecord, Function.update_of_ne (Ne.symm heq), previousValue, heq,
          (hm s (List.mem_cons_of_mem _ hsr)).trans hzero]

/-- The neighboring-record tests on the actual sorted permutation accept
exactly the chronological histories whose read answers are correct. -/
theorem predecessorCheck_iff_readsCorrect {chron sorted : List (Record Word)}
    (hp : chron.Perm sorted) (hc : Chronological chron) (hs : AddressSorted sorted) :
    PredecessorCheck none sorted ↔ ReadsCorrect (fun _ => 0) chron := by
  rw [predecessorCheck_iff_sorted (mem := fun _ => 0) hs (by simp) (by simp [previousValue])]
  rw [readsCorrect_iff_cells, readsCorrect_iff_cells]
  exact forall_congr' fun a => by rw [address_histories_eq hp hc hs a]

/-- Successor messages suffice for blockwise checking, including the case
of an empty block. -/
theorem predecessorCheck_append (previous : Option (Record Word)) (xs ys : List (Record Word)) :
    PredecessorCheck previous (xs ++ ys) ↔
      PredecessorCheck previous xs ∧ PredecessorCheck (xs.getLast?.or previous) ys := by
  induction xs generalizing previous with
  | nil => simp [PredecessorCheck]
  | cons r rs ih =>
    rw [List.cons_append, PredecessorCheck, PredecessorCheck, ih]
    cases rs <;> simp [and_assoc, List.getLast?_cons]

/-- The initialization writes specified by the headers at addresses below S. -/
def initRecord (header : ℕ → Word) (a : ℕ) : Record Word := ⟨.init, a, header a, a, 0⟩

/-- Header initialization writes for the consecutive addresses from zero through `S - 1`,
listed in address order. -/
def initialRecords (S : ℕ) (header : ℕ → Word) : List (Record Word) :=
  (List.range S).map (initRecord header)

/-- External memory with the supplied header words below `S` and zero at every higher address. -/
def initialMemory (S : ℕ) (header : ℕ → Word) (a : ℕ) : Word :=
  if a < S then header a else 0

/-- Processing the synthetic initialization writes installs exactly the header
memory, retaining zero on all other addresses. -/
theorem readsCorrect_initialRecords_append (S : ℕ) (header : ℕ → Word)
    (probes : List (Record Word)) :
    ReadsCorrect (fun _ => 0) (initialRecords S header ++ probes) ↔
      ReadsCorrect (initialMemory S header) probes := by
  induction S generalizing probes with
  | zero =>
    have hz : initialMemory 0 header = fun _ => 0 := by funext a; simp [initialMemory]
    simp [initialRecords, hz]
  | succ S ih =>
    have hlist : initialRecords (S + 1) header = initialRecords S header ++ [initRecord header S] := by
      simp [initialRecords, List.range_succ]
    rw [hlist, List.append_assoc, List.singleton_append, ih, ReadsCorrect]
    have hmem : afterRecord (initialMemory S header) (initRecord header S) =
        initialMemory (S + 1) header := by
      funext a
      by_cases h : a = S
      · subst a
        simp [afterRecord, initRecord, initialMemory]
      · have hequiv : a < S + 1 ↔ a < S := by omega
        simp [afterRecord, initRecord, Function.update_of_ne h, initialMemory, hequiv]
    rw [hmem]
    simp [initRecord]

omit [Zero Word] in
theorem chronological_initialRecords_append {S : ℕ} {header : ℕ → Word}
    {probes : List (Record Word)} (ht : Chronological probes)
    (hprobe : ∀ r ∈ probes, r.kind ≠ .init) :
    Chronological (initialRecords S header ++ probes) := by
  apply List.pairwise_append.mpr
  refine ⟨?_, ht, ?_⟩
  · apply List.pairwise_map.mpr
    exact List.pairwise_lt_range.imp fun h => by
      simp [initRecord, Record.timestamp, Prod.Lex.toLex_lt_toLex, h]
  · intro r hr s hs
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
    simp [initRecord, Record.timestamp, Prod.Lex.toLex_lt_toLex, hprobe s hs]

/-- The nonempty key has four components: address, initialization priority,
starting cost, and ordinal. A padding record is larger than every such key. -/
def paddedKey : Option (Record Word) → WithTop (Lex (ℕ × Lex (ℕ × Lex (ℕ × ℕ))))
  | none => ⊤
  | some r => ↑(toLex (r.address, r.timestamp))

omit [Zero Word] in
theorem addressSorted_of_padded_sort {chron : List (Record Word)}
    {sorted : List (Option (Record Word))} (hp : chron.Perm (sorted.filterMap id))
    (hc : Chronological chron) (hs : sorted.Pairwise fun x y => paddedKey x ≤ paddedKey y) :
    AddressSorted (sorted.filterMap id) := by
  have hle : (sorted.filterMap id).Pairwise fun x y =>
      x.address < y.address ∨ x.address = y.address ∧ x.timestamp ≤ y.timestamp := by
    apply hs.filterMap id
    intro x y h s hx t hy
    change x = some s at hx
    change y = some t at hy
    subst x
    subst y
    simpa [paddedKey, Prod.Lex.toLex_le_toLex] using h
  have hn : (chron.map Record.timestamp).Nodup :=
    List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr (hc.imp fun h => h.ne))
  have hn' := (hp.map Record.timestamp).nodup_iff.mp hn
  have hne := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp hn')
  exact (hle.and hne).imp fun ⟨hord, hd⟩ => hord.imp_right fun ⟨ha, ht⟩ =>
    ⟨ha, lt_of_le_of_ne ht hd⟩

/-- Validation after sorting and removing padding agrees with executing the
probes against the specified headers. The premises on the sort are its usual
permutation and non-strict ordering postconditions. -/
theorem padded_predecessorCheck_iff {S : ℕ} {header : ℕ → Word}
    {probes : List (Record Word)} {raw sorted : List (Option (Record Word))}
    (hrecords : (initialRecords S header ++ probes).Perm (raw.filterMap id))
    (hperm : raw.Perm sorted) (hsorted : sorted.Pairwise fun x y => paddedKey x ≤ paddedKey y)
    (ht : Chronological probes) (hprobe : ∀ r ∈ probes, r.kind ≠ .init) :
    PredecessorCheck none (sorted.filterMap id) ↔ ReadsCorrect (initialMemory S header) probes := by
  have hp := hrecords.trans (hperm.filterMap id)
  have hc := chronological_initialRecords_append (S := S) (header := header) ht hprobe
  exact (predecessorCheck_iff_readsCorrect hp hc (addressSorted_of_padded_sort hp hc hsorted)).trans
    (readsCorrect_initialRecords_append S header probes)

/-- The site validator scans its physical slots, including empties. Its
incoming predecessor field is the final physical slot of the preceding site. -/
def PaddedCheck (previous : Option (Record Word)) : List (Option (Record Word)) → Prop
  | [] => True
  | none :: rs => PaddedCheck none rs
  | some r :: rs => (r.kind = .read → r.value = previousValue previous r.address) ∧
      PaddedCheck (some r) rs

theorem paddedCheck_append (previous : Option (Record Word))
    (xs ys : List (Option (Record Word))) :
    PaddedCheck previous (xs ++ ys) ↔
      PaddedCheck previous xs ∧ PaddedCheck (xs.getLast?.getD previous) ys := by
  induction xs generalizing previous with
  | nil => simp [PaddedCheck]
  | cons r rs ih =>
    cases r with
    | none =>
      rw [List.cons_append, PaddedCheck, PaddedCheck, ih]
      simp [List.getLast?_cons]
    | some r =>
      rw [List.cons_append, PaddedCheck, PaddedCheck, ih]
      simp [List.getLast?_cons, and_assoc]

/-- In a sorted array a padding record cannot interrupt an address history. -/
theorem paddedCheck_iff_filter {sorted : List (Option (Record Word))}
    (hs : sorted.Pairwise fun x y => paddedKey x ≤ paddedKey y) (previous : Option (Record Word)) :
    PaddedCheck previous sorted ↔ PredecessorCheck previous (sorted.filterMap id) := by
  induction sorted generalizing previous with
  | nil => simp [PaddedCheck, PredecessorCheck]
  | cons r rs ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hs
    cases r with
    | none =>
      have hempty : rs.filterMap id = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hx
        change r = some x at he
        subst r
        simpa [paddedKey] using hh _ hr
      rw [PaddedCheck, ih ht none, List.filterMap_cons_none (by rfl), hempty]
      rfl
    | some r => simp [PaddedCheck, PredecessorCheck, ih ht]

/-- Physical site checks, with actual empty slots, recover precisely the
valid RAM reads starting from the headers. -/
theorem paddedCheck_iff_readsCorrect {S : ℕ} {header : ℕ → Word}
    {probes : List (Record Word)} {raw sorted : List (Option (Record Word))}
    (hrecords : (initialRecords S header ++ probes).Perm (raw.filterMap id))
    (hperm : raw.Perm sorted) (hsorted : sorted.Pairwise fun x y => paddedKey x ≤ paddedKey y)
    (ht : Chronological probes) (hprobe : ∀ r ∈ probes, r.kind ≠ .init) :
    PaddedCheck none sorted ↔ ReadsCorrect (initialMemory S header) probes :=
  (paddedCheck_iff_filter hsorted none).trans
    (padded_predecessorCheck_iff hrecords hperm hsorted ht hprobe)

end RAMMemory

end VPVNP
end Computability
end OAI

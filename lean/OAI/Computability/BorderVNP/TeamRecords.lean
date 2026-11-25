import OAI.Computability.VPVNP.RAMMemory
import OAI.Computability.VPVNP.RAMSortCorrect
import OAI.Computability.VPVNP.RAMSortPerm
import Mathlib.Data.List.Perm.Basic

/-!
# Shared-memory records in the team simulation

In §7.2 of *An explicit VNP family requires superpolynomial border circuit size over every
field*, every probe claims the previous word, including a probe which overwrites it. A read
copies that word to the output field. The actual Batcher sort groups records by address and
then time. Its neighboring-record check recovers precisely the unique chronological record
list of the supplied reads and writes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamRecords

open VPVNP

/-- The occupied four-word slot from §7.2. -/
structure Record (Word : Type*) where
  /-- Memory address of the probe. -/
  address : ℕ
  /-- Global tick, zero for initialization. -/
  tick : ℕ
  /-- Guessed previous word. -/
  before : Word
  /-- Word left by the instruction. -/
  after : Word
  deriving DecidableEq

variable {Word : Type*}

/-- Chronological order. Time-zero initialization records are enumerated by address. -/
def Chronological (rs : List (Record Word)) : Prop :=
  rs.Pairwise fun r s => r.tick < s.tick ∨ r.tick = s.tick ∧ r.address < s.address

/-- Sorted active slots, with strict time order inside each address. -/
def AddressSorted (rs : List (Record Word)) : Prop :=
  rs.Pairwise fun r s => r.address < s.address ∨ r.address = s.address ∧ r.tick < s.tick

private def previousWord [Zero Word] (p : Option (Record Word)) (a : ℕ) : Word :=
  match p with
  | none => 0
  | some r => if r.address = a then r.after else 0

/-- Test the previous field against the preceding resulting word, or zero at a new address. -/
def NeighborCheck [Zero Word] (prev : Option (Record Word)) : List (Record Word) → Prop
  | [] => True
  | r :: rs => r.before = previousWord prev r.address ∧ NeighborCheck (some r) rs

/-- Chronological execution of the occupied slots from memory `m`. -/
def MemoryCheck (m : ℕ → Word) : List (Record Word) → Prop
  | [] => True
  | r :: rs => r.before = m r.address ∧ MemoryCheck (Function.update m r.address r.after) rs

/-- Read half of a physical probe, checking the claimed previous word. -/
def inputRecord (r : Record Word) : RAMMemory.Record Word :=
  ⟨.read, r.address, r.before, r.tick, 2 * r.address⟩

/-- Write half of the same probe. Its ordinal immediately follows the read half. -/
def outputRecord (r : Record Word) : RAMMemory.Record Word :=
  ⟨.write, r.address, r.after, r.tick, 2 * r.address + 1⟩

/-- Two ordinary memory records implementing one four-word before/after probe. -/
def pair (r : Record Word) : List (RAMMemory.Record Word) :=
  [inputRecord r, outputRecord r]

/-- Checking all expanded read/write pairs from a memory is equivalent to checking the probes. -/
theorem memoryCheck_pair (rs : List (Record Word)) (m : ℕ → Word) :
    RAMMemory.ReadsCorrect m (rs.flatMap pair) ↔ MemoryCheck m rs := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih =>
    have hread : RAMMemory.afterRecord m (inputRecord r) = m := rfl
    have hwrite : RAMMemory.afterRecord m (outputRecord r) = Function.update m r.address r.after := rfl
    simp only [List.flatMap_cons, pair, List.cons_append, List.nil_append, RAMMemory.ReadsCorrect,
      hread, hwrite, ih, MemoryCheck]
    simp [inputRecord, outputRecord]

private theorem neighborCheck_pair [Zero Word] (rs : List (Record Word)) (p : Option (Record Word)) :
    RAMMemory.PredecessorCheck (p.map outputRecord) (rs.flatMap pair) ↔ NeighborCheck p rs := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih =>
    have h : RAMMemory.PredecessorCheck (some (outputRecord r)) (rs.flatMap pair) ↔
        NeighborCheck (some r) rs := ih (some r)
    simp only [List.flatMap_cons, pair, List.cons_append, List.nil_append,
      RAMMemory.PredecessorCheck, h, NeighborCheck]
    cases p <;> simp [inputRecord, outputRecord, RAMMemory.previousValue, previousWord]
    tauto

/-- Read/write expansion preserves strict chronological ordering, including initializations. -/
theorem pair_chronological {rs : List (Record Word)} (h : Chronological rs) :
    RAMMemory.Chronological (rs.flatMap pair) := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih =>
    obtain ⟨hr, ht⟩ := List.pairwise_cons.mp h
    apply List.pairwise_append.mpr
    refine ⟨?_, ih ht, ?_⟩
    · simp [pair, inputRecord, outputRecord, RAMMemory.Record.timestamp, Prod.Lex.toLex_lt_toLex]
    · intro a ha b hb
      obtain ⟨s, hs, hb⟩ := List.mem_flatMap.mp hb
      have hrs := hr s hs
      simp [pair] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp [inputRecord, outputRecord, RAMMemory.Record.timestamp, Prod.Lex.toLex_lt_toLex] <;>
        omega

private theorem pair_addressSorted {rs : List (Record Word)} (h : AddressSorted rs) :
    RAMMemory.AddressSorted (rs.flatMap pair) := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih =>
    obtain ⟨hr, ht⟩ := List.pairwise_cons.mp h
    apply List.pairwise_append.mpr
    refine ⟨?_, ih ht, ?_⟩
    · simp [pair, inputRecord, outputRecord, RAMMemory.Record.timestamp, Prod.Lex.toLex_lt_toLex]
    · intro a ha b hb
      obtain ⟨s, hs, hb⟩ := List.mem_flatMap.mp hb
      have hrs := hr s hs
      simp [pair] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp [inputRecord, outputRecord, RAMMemory.Record.timestamp, Prod.Lex.toLex_lt_toLex] <;>
        omega

/-- For the paper's four-word records the address-local tests recover every previous word,
including the word overwritten by a write. -/
theorem neighborCheck_iff_memoryCheck [Zero Word] {chron sorted : List (Record Word)}
    (hp : chron.Perm sorted) (ht : Chronological chron) (ha : AddressSorted sorted) :
    NeighborCheck none sorted ↔ MemoryCheck (fun _ => 0) chron := by
  exact (neighborCheck_pair sorted none).symm.trans
    ((RAMMemory.predecessorCheck_iff_readsCorrect (hp.flatMap fun _ _ => .refl _)
      (pair_chronological ht) (pair_addressSorted ha)).trans (memoryCheck_pair ..))

/-- A fixed path specifies each address and the word to be written, if any. -/
structure Access (Word : Type*) where
  /-- Address read or written. -/
  address : ℕ
  /-- Logical time of this probe. -/
  tick : ℕ
  /-- A present value overwrites the word; an absent value denotes a read. -/
  write : Option Word

/-- Fill a record using a local guess for the previous word. -/
def Access.record (e : Access Word) (v : Word) : Record Word :=
  ⟨e.address, e.tick, v, e.write.getD v⟩

/-- Local instruction checks fix the address, tick and action, leaving the old word to be checked. -/
def Matches (es : List (Access Word)) (rs : List (Record Word)) : Prop :=
  List.Forall₂ (fun (e : Access Word) (r : Record Word) => r = e.record r.before) es rs

/-- The records obtained by executing a fixed path from memory `m`. -/
def transcript (m : ℕ → Word) : List (Access Word) → List (Record Word)
  | [] => []
  | e :: es =>
    let r := e.record (m e.address)
    r :: transcript (Function.update m r.address r.after) es

/-- Every chronological execution supplies all the locally prescribed fields. -/
theorem matches_transcript (m : ℕ → Word) (es : List (Access Word)) :
    Matches es (transcript m es) := by
  induction es generalizing m with
  | nil => exact .nil
  | cons e es ih => exact .cons rfl (ih _)

/-- Given the locally prescribed memory actions, a passing chronological transcript is unique. -/
theorem memoryCheck_iff_transcript {es : List (Access Word)} {rs : List (Record Word)}
    (h : Matches es rs) (m : ℕ → Word) : MemoryCheck m rs ↔ rs = transcript m es := by
  induction h generalizing m with
  | nil => simp [MemoryCheck, transcript]
  | @cons e r es rs he _ ih =>
    change r = e.record r.before at he
    constructor
    · rintro ⟨hbefore, hrest⟩
      have hr : r = e.record (m e.address) := by
        have haddr : r.address = e.address := congrArg Record.address he
        exact he.trans (congrArg e.record (hbefore.trans (congrArg m haddr)))
      rw [transcript, ← hr, ih _ |>.mp hrest]
    · intro eqs
      have hr := (List.cons.inj eqs).1
      refine ⟨?_, (ih _).mpr ?_⟩
      · rw [hr]; rfl
      · simpa only [hr] using (List.cons.inj eqs).2

/-- A padding slot compares above occupied slots, with deterministic payload tie-breaking. -/
structure Slot (Word : Type*) where
  /-- The four-word record, or the unique empty slot. -/
  record : Option (Record Word)

/-- Primary address-time key, then previous and resulting words, with padding last. -/
def Slot.code (s : Slot Word) : WithTop (Lex (Lex (ℕ × ℕ) × Lex (Word × Word))) :=
  match s.record with
  | none => ⊤
  | some r => ↑(toLex (toLex (r.address, r.tick), toLex (r.before, r.after)))

private theorem slot_injective : Function.Injective (@Slot.code Word) := by
  rintro ⟨a⟩ ⟨b⟩ h
  cases a with
  | none => cases b <;> simp_all [Slot.code]
  | some r =>
    cases b with
    | none => simp [Slot.code] at h
    | some s =>
      cases r; cases s; simp_all [Slot.code]

instance [LinearOrder Word] : LinearOrder (Slot Word) := LinearOrder.lift' Slot.code slot_injective

/-- The occupied records on the output wires of the actual ascending Batcher network. -/
def sortedRecords [LinearOrder Word] (b : ℕ) (xs : RAMSort.Wires b (Slot Word)) :
    List (Record Word) :=
  (List.ofFn (RAMSort.sort b true xs)).filterMap Slot.record

private theorem perm_sortedRecords [LinearOrder Word] (b : ℕ) (xs : RAMSort.Wires b (Slot Word)) :
    ((List.ofFn xs).filterMap Slot.record).Perm (sortedRecords b xs) :=
  (RAMSort.sort_perm b true xs).symm.filterMap _

private theorem addressSorted_sortedRecords [LinearOrder Word] {chron : List (Record Word)}
    {b : ℕ} {xs : RAMSort.Wires b (Slot Word)}
    (hp : chron.Perm ((List.ofFn xs).filterMap Slot.record)) (ht : Chronological chron) :
    AddressSorted (sortedRecords b xs) := by
  have hs : (List.ofFn (RAMSort.sort b true xs)).Pairwise (· ≤ ·) := by
    exact List.pairwise_ofFn.mpr fun _ _ h => RAMSort.sort_monotone _ _ h.le
  have hweak : (sortedRecords b xs).Pairwise fun r s =>
      r.address < s.address ∨ r.address = s.address ∧ r.tick ≤ s.tick := by
    apply hs.filterMap Slot.record
    rintro ⟨x⟩ ⟨y⟩ h r hxr s hys
    change x = some r at hxr
    change y = some s at hys
    subst x; subst y
    change Slot.code ⟨some r⟩ ≤ Slot.code ⟨some s⟩ at h
    simp only [Slot.code, WithTop.coe_le_coe,
      Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_lt_toLex] at h
    rcases h with ha | ⟨ha, _⟩
    · omega
    · have he := congrArg ofLex ha
      exact Or.inr ⟨congrArg Prod.fst he, (congrArg Prod.snd he).le⟩
  let key (r : Record Word) := (r.address, r.tick)
  have hn : (chron.map key).Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    apply List.pairwise_map.mpr
    exact ht.imp fun hr he => by
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      simp only [key] at h₁ h₂
      omega
  have hn' := ((hp.trans (perm_sortedRecords b xs)).map key).nodup_iff.mp hn
  have hne := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp hn')
  exact (hweak.and hne).imp fun ⟨hw, hd⟩ => hw.imp_right fun ⟨ha, ht'⟩ =>
    ⟨ha, lt_of_le_of_ne ht' fun he => hd (Prod.ext ha he)⟩

/-- The valid order of probes in a path. Distinct initialization addresses may share tick zero. -/
def Timed (es : List (Access Word)) : Prop :=
  (es.map fun e => toLex (e.tick, e.address)).Pairwise (· < ·)

/-- The timestamps and addresses on a matching record trace inherit the instruction order. -/
theorem chronological_of_matches {es : List (Access Word)} {rs : List (Record Word)}
    (he : Matches es rs) (ht : Timed es) : Chronological rs := by
  have keys : (rs.map fun r => toLex (r.tick, r.address)) = es.map fun e => toLex (e.tick, e.address) := by
    clear ht
    induction he with
    | nil => rfl
    | cons h _ ih =>
      simp only [List.map_cons, ih, List.cons.injEq, and_true]
      rw [h]
      rfl
  change (es.map fun e => toLex (e.tick, e.address)).Pairwise (· < ·) at ht
  rw [← keys] at ht
  exact (List.pairwise_map.mp ht).imp fun h => Prod.Lex.toLex_lt_toLex.mp h

/-- Running the actual Batcher network and testing its neighbors accepts precisely the unique
transcript of the specified path, even when the physical inputs are arbitrarily interleaved
among processors and padded with empty records. -/
theorem sortedCheck_iff_transcript [LinearOrder Word] [Zero Word] {es : List (Access Word)}
    {rs : List (Record Word)} {b : ℕ} {xs : RAMSort.Wires b (Slot Word)}
    (he : Matches es rs) (ht : Timed es)
    (hp : rs.Perm ((List.ofFn xs).filterMap Slot.record)) :
    NeighborCheck none (sortedRecords b xs) ↔ rs = transcript (fun _ => 0) es :=
  let hchron := chronological_of_matches he ht
  (neighborCheck_iff_memoryCheck (hp.trans (perm_sortedRecords b xs)) hchron
    (addressSorted_sortedRecords hp hchron)).trans (memoryCheck_iff_transcript he _)

private theorem exists_padded_input {rs : List (Record Word)} {b : ℕ} (hfit : rs.length ≤ 2 ^ b) :
    ∃ xs : RAMSort.Wires b (Slot Word), (List.ofFn xs).filterMap Slot.record = rs := by
  let padded := rs.map (fun r => Slot.mk (some r)) ++ List.replicate (2 ^ b - rs.length) ⟨none⟩
  have hlen : padded.length = 2 ^ b := by simp [padded, Nat.add_sub_cancel' hfit]
  let xs : RAMSort.Wires b (Slot Word) := fun i => padded[i.val]'(by rw [hlen]; exact i.isLt)
  have hraw : List.ofFn xs = padded := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hi'
      simp [xs]
  refine ⟨xs, ?_⟩
  rw [hraw]
  simp [padded, List.filterMap_map]

/-- For every timed path that fits in the padded array there is exactly one chronological
list of previous and resulting words with a successful sort and local neighbor checks. -/
theorem existsUnique_sorted_transcript [LinearOrder Word] [Zero Word] (es : List (Access Word))
    {b : ℕ} (ht : Timed es) (hfit : es.length ≤ 2 ^ b) :
    ∃! rs, Matches es rs ∧ ∃ xs : RAMSort.Wires b (Slot Word),
      rs.Perm ((List.ofFn xs).filterMap Slot.record) ∧ NeighborCheck none (sortedRecords b xs) := by
  let rs := transcript (fun _ => 0) es
  have hm : Matches es rs := matches_transcript ..
  obtain ⟨xs, hxs⟩ := exists_padded_input (hm.length_eq ▸ hfit)
  refine ⟨rs, ⟨hm, xs, hxs ▸ .refl _, ?_⟩, ?_⟩
  · exact (sortedCheck_iff_transcript hm ht (hxs ▸ .refl _)).mpr rfl
  · rintro candidate ⟨hlocal, ys, hperm, hcheck⟩
    exact (sortedCheck_iff_transcript hlocal ht hperm).mp hcheck

/-- Each prescribed input word occupies its own address, with timestamp zero. -/
def initialization (S : ℕ) (header : ℕ → Word) : List (Access Word) :=
  (List.range S).map fun a => ⟨a, 0, some (header a)⟩

/-- Time-zero initialization can precede any correctly ordered trace beginning at tick one. -/
theorem timed_initialization {S : ℕ} {header : ℕ → Word} {es : List (Access Word)}
    (ht : Timed es) (hpos : ∀ e ∈ es, 0 < e.tick) : Timed (initialization S header ++ es) := by
  simp only [Timed, List.map_append, List.pairwise_append, initialization, List.map_map]
  refine ⟨?_, ht, ?_⟩
  · apply List.pairwise_map.mpr
    exact List.pairwise_lt_range.imp fun h => by simpa [Prod.Lex.toLex_lt_toLex] using h
  · intro x hx y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (hpos e he))

/-- Initialization claims zero even on writes and installs precisely the prescribed header.
All subsequent records start from that memory. -/
theorem transcript_initialization [Zero Word] (S : ℕ) (header : ℕ → Word) (es : List (Access Word)) :
    transcript (fun _ => 0) (initialization S header ++ es) =
      (List.range S).map (fun a => ⟨a, 0, 0, header a⟩) ++
        transcript (RAMMemory.initialMemory S header) es := by
  induction S generalizing es with
  | zero =>
    have hm : RAMMemory.initialMemory 0 header = fun _ => 0 := by
      funext a
      simp [RAMMemory.initialMemory]
    simp [initialization, hm]
  | succ S ih =>
    have hinit : initialization (S + 1) header =
        initialization S header ++ [⟨S, 0, some (header S)⟩] := by
      simp [initialization, List.range_succ]
    have hm : Function.update (RAMMemory.initialMemory S header) S (header S) =
        RAMMemory.initialMemory (S + 1) header := by
      funext a
      by_cases ha : a = S
      · subst a; simp [RAMMemory.initialMemory]
      · have hlt : a < S + 1 ↔ a < S := by omega
        simp [Function.update_of_ne ha, RAMMemory.initialMemory, hlt]
    rw [hinit, List.append_assoc, ih, List.range_succ]
    simp [transcript, Access.record, RAMMemory.initialMemory, hm]

/-- A local subroutine reads `q` consecutive words on its first `q` ticks.
The remaining tick of its `q+1` charge emits no memory record. -/
def readBurst (a t : ℕ) : ℕ → List (Access Word)
  | 0 => []
  | q + 1 => ⟨a, t, none⟩ :: readBurst (a + 1) (t + 1) q

/-- Consecutive subroutine reads preserve memory, including the words visible to following
instructions. The returned record at offset `i` contains exactly the word at `a+i`. -/
theorem transcript_readBurst (m : ℕ → Word) (a t q : ℕ) (es : List (Access Word)) :
    transcript m (readBurst a t q ++ es) =
      (List.ofFn fun i : Fin q => ⟨a + i.val, t + i.val, m (a + i.val), m (a + i.val)⟩) ++
        transcript m es := by
  induction q generalizing a t with
  | zero => simp [readBurst]
  | succ q ih =>
    rw [List.ofFn_succ]
    simp [readBurst, transcript, Access.record, Function.update_eq_self, ih,
      Nat.add_assoc, Nat.add_comm 1]

end TeamRecords

end BorderVNP
end Computability
end OAI

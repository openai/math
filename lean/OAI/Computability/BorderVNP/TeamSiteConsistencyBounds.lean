import OAI.Computability.BorderVNP.TeamSiteConsistencyRows

/-! # Word bounds and slot capacity of the interleaved processor rows

The interval check permits a burst ending exactly at the word modulus. Each accessed
address still lies strictly below that endpoint. A chronological instruction consumes
one tick plus its burst length. Every input bit and every actual probe emits two slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP TeamRAM TeamEventRecords
open BurstRAM (Word)
variable {w r : ℕ} {S : Type*}

private theorem burstBounds (a t q : ℕ) (vs : List (Word w))
    (ha : a+q ≤ 2^w) (ht : t+q ≤ 2^w) :
    ∀ z ∈ (TeamRecords.readBurst a t q).zipWith TeamRecords.Access.record vs,
      z.address < 2^w ∧ z.tick < 2^w := by
  induction q generalizing a t vs with
  | zero => simp [TeamRecords.readBurst]
  | succ q ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · exact ⟨by change a < _; omega, by change t < _; omega⟩
      · exact ih (a+1) (t+1) vs (by omega) (by omega) _ h

private theorem fetchedBounds (i : Instr w S) (e : Event w) (t : ℕ)
    (fetch : i.action = some e.action) (time : t+(1+e.action.extra) ≤ 2^w) :
    ∀ z ∈ eventFields t e, z.address < 2^w ∧ z.tick < 2^w := by
  obtain ⟨act,vs,bs,sg⟩ := e
  cases i with
  | accept | reject => contradiction
  | localStep n v | choose n =>
    cases fetch
    simp [eventFields,TeamTranscript.Action.accesses]
  | load a n | store a v n =>
    cases fetch
    have htime : t < 2^w := by change t+(1+0) ≤ 2^w at time; omega
    cases vs <;> simp [eventFields,TeamTranscript.Action.accesses,TeamRecords.Access.record,a.isLt,htime]
  | call a q fn n =>
    change (if a.val+q ≤ 2^w then some (.burst a.val q) else none) = some act at fetch
    split at fetch <;> try contradiction
    cases fetch
    change t+(1+q) ≤ 2^w at time
    exact burstBounds a.val t q vs ‹a.val+q ≤ 2^w› (by omega)

/-- Addresses and ticks of every locally admitted execution are represented without
wraparound, including the last word of a burst reaching the top of address space. -/
theorem historyFields_bounds {P : S → Instr w S} {start : S} {t : ℕ} {es : List (Event w)}
    (localRun : Local P start es) (budget : t+RAMBuckets.cost (fun e => e.action.extra) es ≤ 2^w) :
    ∀ z ∈ historyFields t es, z.address < 2^w ∧ z.tick < 2^w := by
  induction es generalizing start t with
  | nil => simp [historyFields]
  | cons e es ih =>
    obtain ⟨fetch,next,_,rest⟩ := localRun
    change t+((1+e.action.extra)+RAMBuckets.cost _ es) ≤ 2^w at budget
    intro z hz
    rcases List.mem_append.mp hz with head | tail
    · exact fetchedBounds (P start) e t fetch (by omega) _ head
    · exact ih rest (t := t+(1+e.action.extra)) (by omega) _ tail

private theorem inputFits (a : ℕ) (bs : List Bool) (bound : a+bs.length ≤ 2^w) :
    ∀ z ∈ TeamTapeInputEmit.probes (w+1) a bs, TeamTapeSorting.ProbeFits z := by
  induction bs generalizing a with
  | nil => simp [TeamTapeInputEmit.probes]
  | cons b bs ih =>
    simp only [List.length_cons] at bound
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨TeamTapeSorting.doubledAddress_fits (by omega : a < 2^w), Nat.two_pow_pos _⟩
    · exact ih (a+1) (by omega) _ hz

/-- In any real row, the phase ordinal, address and time all fit the widened word.
The hypothesis on the RAM path applies to the joined blocks at their global tick. -/
theorem rowFields_fit {P : S → Instr w S} {start : S} (input : Fin r → List Bool)
    (blocks : Fin r → List (Event w)) (localRun : Local P start (List.ofFn blocks).flatten)
    (time : 1+RAMBuckets.cost (fun e => e.action.extra) (List.ofFn blocks).flatten ≤ 2^w)
    (header : (List.ofFn input).flatten.length ≤ 2^w) (j : Fin r) :
    ∀ z ∈ rowFields input blocks j, TeamTapeSorting.ProbeFits z := by
  intro z hz
  have hz' := (chronology_perm input blocks).mem_iff.mpr
    (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,hz⟩)
  rcases List.mem_append.mp hz' with hi | he
  · exact inputFits 0 _ (by simpa using header) _ hi
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
    obtain ⟨ha,ht⟩ := historyFields_bounds localRun time v hv
    exact TeamProbeEmit.probeFits_widenRecord v ha ht

/-- The last bit of each physical input segment stays inside the global header. -/
theorem row_input_size (input : Fin r → List Bool) (header : (List.ofFn input).flatten.length ≤ 2^w)
    (j : Fin r) : 2*(TeamTapeInputEmit.rowStart input j + (input j).length) ≤ 2^(w+1) := by
  let xs := List.ofFn input
  have cut := congrArg (fun ys : List (List Bool) => ys.flatten.length)
    (List.take_append_drop (j.val+1) xs)
  rw [List.flatten_append, List.length_append,
    List.take_succ_eq_append_getElem (by simp [xs]),
    List.flatten_append,List.length_append] at cut
  simp only [xs, List.flatten_cons, List.flatten_nil,List.append_nil,List.getElem_ofFn] at cut
  change (TeamTapeInputEmit.rowStart input j + (input j).length) +
    (xs.drop (j.val+1)).flatten.length = xs.flatten.length at cut
  change xs.flatten.length ≤ 2^w at header
  rw [pow_succ]
  omega

private theorem historyFields_length (t : ℕ) (es : List (Event w)) :
    (historyFields t es).length ≤ (TeamTranscript.probes Event.action t es).length := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    simp only [historyFields,TeamTranscript.probes,List.length_append,eventFields,List.length_zipWith]
    exact Nat.add_le_add (Nat.min_le_left ..) (ih _)

/-- One locally charged tick accounts for at most one four-field logical probe. -/
theorem historyFields_length_le (t : ℕ) (es : List (Event w)) :
    (historyFields t es).length ≤ RAMBuckets.cost (fun e => e.action.extra) es :=
  (historyFields_length t es).trans (TeamTranscript.probes_spec Event.action t es).1

private theorem pairs_length (xs : List (TeamRecords.Record (Word w))) :
    (xs.flatMap TeamRecords.pair).length = 2*xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
    rw [List.flatMap_cons,List.length_append,List.length_cons,ih]
    change 2+2*xs.length = 2*(xs.length+1); omega

/-- The concrete sorter occupies exactly two slots for each emitted event record. -/
theorem historySlots_length (t : ℕ) (es : List (Event w)) :
    (historySlots t es).length = 2*(historyFields t es).length := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    simp only [historySlots,TeamEventRecords.historySlots,historyFields,physicalSlots,physicalFields,List.length_append,
      List.length_map,pairs_length,ih,Nat.mul_add]

/-- Input and instruction slots together fit a physical block of eight slots per
logical block tick when the input segment has at most three bits per tick. -/
theorem realRows_length_le (input : Fin r → List Bool) (blocks : Fin r → List (Event w))
    (j : Fin r) (H : ℕ) (header : (input j).length ≤ 3*H)
    (cost : RAMBuckets.cost (fun e => e.action.extra) (blocks j) ≤ H) :
    (realRows input blocks j).length ≤ 8*H := by
  simp only [realRows,List.length_append,TeamTapeInputEmit.length_records,historySlots_length]
  have := (historyFields_length_le (1+blockOffset blocks j) (blocks j)).trans cost
  omega

private theorem input_length (k a : ℕ) (bs : List Bool) :
    (TeamTapeInputEmit.probes k a bs).length = bs.length := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => exact congrArg (·+1) (ih _)

/-- The same physical capacity in the logical-row interface of the sorter. -/
theorem rowFields_length_le (input : Fin r → List Bool) (blocks : Fin r → List (Event w))
    (j : Fin r) (H : ℕ) (header : (input j).length ≤ 3*H)
    (cost : RAMBuckets.cost (fun e => e.action.extra) (blocks j) ≤ H) :
    (rowFields input blocks j).length ≤ 4*H := by
  simp only [rowFields,List.length_append,input_length,List.length_map]
  exact Nat.add_le_add header ((historyFields_length_le _ _).trans cost) |>.trans (by omega)

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI

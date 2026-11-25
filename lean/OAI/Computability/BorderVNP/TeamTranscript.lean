import OAI.Computability.BorderVNP.TeamBlocks
import OAI.Computability.BorderVNP.TeamSorting
import OAI.Computability.BorderVNP.TeamScales
import Mathlib.Data.List.FinRange

/-!
# Weighted RAM histories in processor teams

In §7.2 of *An explicit VNP family requires superpolynomial border circuit size
over every field*, an ordinary instruction can access at most one word and a
local subroutine can read a consecutive interval. Fixing a path fixes these
operations, their private choices and their weights. The greedy processor
boundaries, guessed words and physical sorting messages are then uniquely
recoverable from their local checks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTranscript

open Filter VPVNP

/-- Memory action specified by a path at one instruction. Ordinary instructions can
omit the probe, read its address, or write a new value. A subroutine reads a burst. -/
inductive Action (Word : Type*) where
  | ordinary (probe : Option (ℕ × Option Word))
  | burst (start length : ℕ)

variable {Word A : Type*}

/-- Extra ticks charged for subroutine input. -/
def Action.extra : Action Word → ℕ
  | .ordinary _ => 0
  | .burst _ q => q

/-- Records emitted by an instruction starting at a given tick. -/
def Action.accesses (t : ℕ) : Action Word → List (TeamRecords.Access Word)
  | .ordinary none => []
  | .ordinary (some (a, v)) => [⟨a, t, v⟩]
  | .burst a q => TeamRecords.readBurst a t q

private theorem burst_bounds (a t q : ℕ) :
    let es := TeamRecords.readBurst (Word := Word) a t q
    es.length = q ∧ es.Pairwise (fun e f => e.tick < f.tick) ∧
      ∀ e ∈ es, t ≤ e.tick ∧ e.tick < t + q := by
  induction q generalizing a t with
  | zero => simp [TeamRecords.readBurst]
  | succ q ih =>
    obtain ⟨hlen, hp, hb⟩ := ih (a + 1) (t + 1)
    simp only [TeamRecords.readBurst, List.length_cons, hlen, List.pairwise_cons, true_and]
    refine ⟨⟨fun e he => (hb e he).1, hp⟩, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · have := hb e he; omega

private theorem action_bounds (t : ℕ) (x : Action Word) :
    (x.accesses t).length ≤ 1 + x.extra ∧
    (x.accesses t).Pairwise (fun e f => e.tick < f.tick) ∧
    ∀ e ∈ x.accesses t, t ≤ e.tick ∧ e.tick < t + (1 + x.extra) := by
  cases x with
  | ordinary p =>
    cases p with
    | none => simp [Action.accesses, Action.extra]
    | some p => obtain ⟨a, v⟩ := p; simp [Action.accesses, Action.extra]
  | burst a q =>
    obtain ⟨hlen, hp, hb⟩ := burst_bounds (Word := Word) a t q
    refine ⟨by simp [Action.accesses, Action.extra, hlen], hp, ?_⟩
    intro e he
    have ⟨hlo, hhi⟩ := hb e he
    exact ⟨hlo, by simp only [Action.extra]; omega⟩

/-- Chronological probes of a path, with the actual one-plus-burst tick charges. -/
def probes (action : A → Action Word) : ℕ → List A → List (TeamRecords.Access Word)
  | _, [] => []
  | t, x :: xs => (action x).accesses t ++ probes action (t + (1 + (action x).extra)) xs

/-- A path produces at most one record per charged tick. Its occupied slots are
strictly increasing in time, including when consecutive instructions share an address. -/
theorem probes_spec (action : A → Action Word) (t : ℕ) (xs : List A) :
    let es := probes action t xs
    es.length ≤ RAMBuckets.cost (fun x => (action x).extra) xs ∧
      es.Pairwise (fun e f => e.tick < f.tick) ∧ ∀ e ∈ es, t ≤ e.tick := by
  induction xs generalizing t with
  | nil => simp [probes, RAMBuckets.cost]
  | cons x xs ih =>
    have ⟨hlen, horder, htime⟩ := action_bounds t (action x)
    have ⟨hrest, horder', htime'⟩ := ih (t + (1 + (action x).extra))
    simp only [probes, List.length_append, RAMBuckets.cost, List.pairwise_append]
    refine ⟨Nat.add_le_add hlen hrest, ⟨horder, horder', fun e he f hf =>
      (htime e he).2.trans_le (htime' f hf)⟩, ?_⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact (htime e he).1
    · exact (Nat.le_add_right ..).trans (htime' _ he)

/-- All prescribed inputs are written at time zero. Logical instructions start at one. -/
def accesses (action : A → Action Word) (S : ℕ) (header : ℕ → Word) (xs : List A) :
    List (TeamRecords.Access Word) := TeamRecords.initialization S header ++ probes action 1 xs

/-- The chronology required by the adjacent-record test follows from the path clock. -/
theorem accesses_timed (action : A → Action Word) (S : ℕ) (header : ℕ → Word) (xs : List A) :
    TeamRecords.Timed (accesses action S header xs) := by
  have ⟨_, ho, hpos⟩ := probes_spec action 1 xs
  apply TeamRecords.timed_initialization _ hpos
  exact List.pairwise_map.mpr (ho.imp fun h => Prod.Lex.toLex_lt_toLex.mpr (Or.inl h))

/-- For all sufficiently large lengths the processor boundary tests uniquely split
every admissible path, uniformly over positive team sizes. -/
theorem eventually_unique_blocks {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3 / 2)
    (action : A → Action Word) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 0 < r → ∀ xs : List A,
      (∀ x ∈ xs, (action x).extra ≤ TeamScales.width n (1 / 2)) →
      RAMBuckets.cost (fun x => (action x).extra) xs ≤ TeamScales.ticks ξ r n →
      ∃! bs : List (List A), bs.length = r ∧ bs.flatten = xs ∧
        Team.ValidBlocks (fun x => (action x).extra) (TeamScales.block ξ n) bs := by
  filter_upwards [TeamScales.eventually_ticks_fit hξ hξ'] with n hcap
  intro r hr xs bounded ht
  exact Team.existsUnique_teamBlocks _ _ _ _ _ bounded (ht.trans (hcap _ hr).le)

/-- At most three blocks of initialization plus one block of genuine instruction records
suffice for the initial sorting array. -/
theorem accesses_length_le {ξ : ℝ} {r n S : ℕ} (action : A → Action Word) (header : ℕ → Word)
    (xs : List A) (hi : S ≤ r * (3 * TeamScales.block ξ n))
    (ht : RAMBuckets.cost (fun x => (action x).extra) xs ≤ r * TeamScales.block ξ n) :
    (accesses action S header xs).length ≤
      2 ^ (Nat.clog 2 (4 * TeamScales.block ξ n) + Nat.clog 2 r) := by
  have hp := (probes_spec action 1 xs).1
  rw [accesses, List.length_append, TeamRecords.initialization, List.length_map, List.length_range]
  calc
    _ ≤ r * (3 * TeamScales.block ξ n) + r * TeamScales.block ξ n := Nat.add_le_add hi (hp.trans ht)
    _ = (4 * TeamScales.block ξ n) * r := by ring
    _ ≤ 2 ^ Nat.clog 2 (4 * TeamScales.block ξ n) * 2 ^ Nat.clog 2 r :=
      Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)
    _ = _ := (Nat.pow_add ..).symm


private def padded (rs : List (TeamRecords.Record Word)) (N : ℕ) : List (TeamRecords.Slot Word) :=
  rs.map (fun r => ⟨some r⟩) ++ List.replicate (N - rs.length) ⟨none⟩

/-- A placement of the chronological records into physical input slots. The permutation
allows local initialization and execution records to occupy consecutive slots at their owner. -/
def slotInput {b : ℕ} (place : Equiv.Perm (Fin (2 ^ b))) (rs : List (TeamRecords.Record Word))
    (i : ℕ) : TeamRecords.Slot Word :=
  if hi : i < 2 ^ b then ((padded rs (2 ^ b))[(place ⟨i, hi⟩).val]?).getD ⟨none⟩ else ⟨none⟩

private theorem slotInput_perm {b : ℕ} (place : Equiv.Perm (Fin (2 ^ b)))
    (rs : List (TeamRecords.Record Word)) (hfit : rs.length ≤ 2 ^ b) :
    rs.Perm ((List.ofFn (RAMSort.block b 0 (slotInput place rs))).filterMap TeamRecords.Slot.record) := by
  let p := padded rs (2 ^ b)
  have hlen : p.length = 2 ^ b := by simp [p, padded, Nat.add_sub_cancel' hfit]
  let f (i : Fin (2 ^ b)) := p[i.val]'(by rw [hlen]; exact i.isLt)
  have hf : List.ofFn f = p := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj; simp [f]
  have hblock : RAMSort.block b 0 (slotInput place rs) = f ∘ place := by
    funext i
    have hpos : (place i).val < p.length := by rw [hlen]; exact (place i).isLt
    simp [RAMSort.block, slotInput, i.isLt, f, p, List.getElem?_eq_getElem (l := p) hpos]
  rw [hblock]
  have hp := ((place.ofFn_comp_perm f).symm).filterMap TeamRecords.Slot.record
  simpa only [hf, p, padded, List.filterMap_append, List.filterMap_map,
    Function.comp_def, List.filterMap_some, List.filterMap_replicate, List.append_nil] using hp

/-- A typed history records all processor chunks, the four-word chronological
transcript, and the actual cross-block messages of the Batcher network. -/
structure History (A Word : Type*) (r h : ℕ) where
  /-- Instructions and their chosen private data at each processor. -/
  chunks : List (List A)
  /-- Chronological records, including time-zero initialization. -/
  records : List (TeamRecords.Record Word)
  /-- Data sent by a block on each cross-block comparison layer. -/
  sends : RAMLayout.Layer (Nat.clog 2 r) → Fin (2 ^ Nat.clog 2 r) → RAMSort.Wires h (TeamRecords.Slot Word)
  /-- Record sent across each boundary between two adjacent sorted blocks. -/
  boundary : TeamSorting.Boundary (2 ^ Nat.clog 2 r) Word

/-- The local replays test their own adjacent words and the predecessor record on
each incoming boundary. The outgoing value is the final record of the local block. -/
def History.Boundaries [LinearOrder Word] [Zero Word] {r h : ℕ} (t : History A Word r h)
    (hr : 0 < r) (place : Equiv.Perm (Fin (2 ^ (h + Nat.clog 2 r)))) : Prop :=
  ∀ j, ∀ v : TeamSorting.Owned hr j, TeamSorting.BoundaryAt (Nat.two_pow_pos h) t.boundary v.val
    (RAMSort.replay v.val _ (RAMSort.physicalFieldsEquiv.{_,0} h (Nat.clog 2 r) _ t.sends)
      (RAMSort.block h v.val.val (slotInput place t.records)))

/-- The processor stop rule, local instruction fields, cross-block sends and neighboring
word comparisons that must pass for the path `xs`. -/
def History.Valid [LinearOrder Word] [Zero Word] {r h : ℕ} (t : History A Word r h)
    (hr : 0 < r) (H : ℕ) (action : A → Action Word) (S : ℕ) (header : ℕ → Word)
    (place : Equiv.Perm (Fin (2 ^ (h + Nat.clog 2 r)))) (xs : List A) : Prop :=
  t.chunks.length = r ∧ t.chunks.flatten = xs ∧ Team.ValidBlocks (fun x => (action x).extra) H t.chunks ∧
  TeamRecords.Matches (accesses action S header xs) t.records ∧
  (∀ j, TeamSorting.ChecksAt hr t.sends (slotInput place t.records) j) ∧
  t.Boundaries hr place

/-- Product of the path weights recorded locally by the processors, in processor order. -/
def History.weight {M : Type*} [Monoid M] {r h : ℕ} (t : History A Word r h) (w : A → M) : M :=
  (t.chunks.map fun chunk => (chunk.map w).prod).prod

/-- All local multiplications retain the weight of the global chronological path. -/
theorem History.Valid.weight_eq {M : Type*} [Monoid M] [LinearOrder Word] [Zero Word] {r h H S : ℕ}
    {t : History A Word r h} {hr : 0 < r} {action : A → Action Word} {header : ℕ → Word}
    {place : Equiv.Perm (Fin (2 ^ (h + Nat.clog 2 r)))} {xs : List A}
    (valid : t.Valid hr H action S header place xs) (w : A → M) :
    t.weight w = (xs.map w).prod := Team.prod_block_weights w valid.2.1

/-- Passing the local boundary and send tests forces the global chronological memory
record, including the guessed old words at store instructions. -/
theorem History.Valid.records_eq [LinearOrder Word] [Zero Word] {r h H S : ℕ}
    {t : History A Word r h} {hr : 0 < r} {action : A → Action Word} {header : ℕ → Word}
    {place : Equiv.Perm (Fin (2 ^ (h + Nat.clog 2 r)))} {xs : List A}
    (valid : t.Valid hr H action S header place xs)
    (fit : (accesses action S header xs).length ≤ 2 ^ (h + Nat.clog 2 r)) :
    t.records = TeamRecords.transcript (fun _ => 0) (accesses action S header xs) := by
  obtain ⟨_, _, _, hm, hs, hb⟩ := valid
  apply (TeamSorting.existsUnique_boundary_iff_transcript hr t.sends _ hs hm (accesses_timed ..)
    (slotInput_perm place t.records (hm.length_eq ▸ fit))).mp
  refine ⟨t.boundary, hb, fun other ho => ?_⟩
  exact TeamSorting.boundary_ext (Nat.two_pow_pos h) _
    (fun v => ho (TeamSorting.owner hr v) ⟨v, rfl⟩) (fun v => hb (TeamSorting.owner hr v) ⟨v, rfl⟩)

/-- Below the effective tick capacity, a path has one accepted typed history at every
fixed physical placement of its records. Neither old words nor sorting sends contribute
additional path multiplicity. -/
theorem existsUnique_history [LinearOrder Word] [Zero Word] {r : ℕ} (hr : 0 < r)
    (h H maxBurst : ℕ) (action : A → Action Word) (S : ℕ) (header : ℕ → Word)
    (place : Equiv.Perm (Fin (2 ^ (h + Nat.clog 2 r)))) (xs : List A)
    (bounded : ∀ x ∈ xs, (action x).extra ≤ maxBurst)
    (cap : RAMBuckets.cost (fun x => (action x).extra) xs ≤ r * (H - maxBurst))
    (fit : (accesses action S header xs).length ≤ 2 ^ (h + Nat.clog 2 r)) :
    ∃! t : History A Word r h, t.Valid hr H action S header place xs := by
  obtain ⟨bs, hb, hub⟩ := Team.existsUnique_teamBlocks _ H maxBurst r xs bounded cap
  let es := accesses action S header xs
  let rs := TeamRecords.transcript (fun _ => 0) es
  have hm : TeamRecords.Matches es rs := TeamRecords.matches_transcript ..
  have ht : TeamRecords.Timed es := accesses_timed ..
  obtain ⟨ss, hs, hus⟩ := TeamSorting.existsUnique_sends hr h (slotInput place rs)
  have hp := slotInput_perm place rs (hm.length_eq ▸ fit)
  obtain ⟨boundary, hboundary, unique_boundary⟩ :=
    (TeamSorting.existsUnique_boundary_iff_transcript hr ss _ hs hm ht hp).mpr rfl
  let t : History A Word r h := ⟨bs, rs, ss, boundary⟩
  refine ⟨t, ⟨hb.1, hb.2.1, hb.2.2, hm, hs, hboundary⟩, ?_⟩
  intro t' hv
  obtain ⟨bs', rs', ss', boundary'⟩ := t'
  obtain rfl : rs' = rs := hv.records_eq fit
  obtain ⟨hn', hf', hb', _, hs', hc'⟩ := hv
  obtain rfl : bs' = bs := hub bs' ⟨hn', hf', hb'⟩
  obtain rfl := hus ss' hs'
  obtain rfl := unique_boundary boundary' hc'
  rfl

/-- Quantitative, weight-preserving transcript extension at the exact tick cutoff of
Lemma 7.1, uniformly in team size. The prescribed initialization field can include the
literal, exterior links and optional second pin field (at most `3H` bits per processor). -/
theorem eventually_unique_weighted_history {M : Type*} [Monoid M] [LinearOrder Word] [Zero Word]
    {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3 / 2) (action : A → Action Word) (w : A → M) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, ∀ hr : 0 < r, ∀ S : ℕ, S ≤ r * (3 * TeamScales.block ξ n) →
      ∀ (header : ℕ → Word) (xs : List A),
      (∀ x ∈ xs, (action x).extra ≤ TeamScales.width n (1 / 2)) →
      RAMBuckets.cost (fun x => (action x).extra) xs ≤ TeamScales.ticks ξ r n →
      let h := Nat.clog 2 (4 * TeamScales.block ξ n)
      ∀ place : Equiv.Perm (Fin (2 ^ (h + Nat.clog 2 r))), ∃! t : History A Word r h,
        t.Valid hr (TeamScales.block ξ n) action S header place xs ∧ t.weight w = (xs.map w).prod := by
  filter_upwards [TeamScales.eventually_ticks_fit hξ hξ'] with n hcap
  intro r hr S hi header xs bounded ht h place
  have hc := ht.trans (hcap r hr).le
  have hp := accesses_length_le action header xs hi (hc.trans (Nat.mul_le_mul_left _ (Nat.sub_le ..)))
  obtain ⟨t, hv, hu⟩ := existsUnique_history hr h _ _ action S header place xs bounded hc hp
  exact ⟨t, ⟨hv, hv.weight_eq w⟩, fun t' ht' => hu t' ht'.1⟩

end TeamTranscript

end BorderVNP
end Computability
end OAI

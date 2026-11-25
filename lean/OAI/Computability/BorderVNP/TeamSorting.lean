import OAI.Computability.BorderVNP.TeamRecords
import OAI.Computability.BorderVNP.TeamScales
import OAI.Computability.VPVNP.RAMRecordIndex
import OAI.Computability.VPVNP.RAMSortFieldEquiv
import Mathlib.Data.Nat.Log

/-!
# Routing the team record sort

In Lemma 7.1 the number of processors need not be a power of two. The next power of two
supplies the block addresses for the XOR sorting schedule. Each extra block belongs to one
of the initial processors. Physical send checks at these owners determine all messages and
recover the sorted array of four-word records, with the empty slots last.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSorting

open VPVNP RAMSort

/-- Power-of-two padding requires strictly fewer than twice the original number of blocks. -/
theorem padding_lt_twice {r : ℕ} (hr : 0 < r) : 2 ^ Nat.clog 2 r < 2 * r := by
  by_cases he : r = 1
  · simp [he]
  · have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by decide) (show 1 < r by omega)
    rw [Nat.pred_eq_sub_one] at hpred
    have hpos := Nat.clog_pos (b := 2) (by decide) (show 1 < r by omega)
    have h : Nat.clog 2 r = (Nat.clog 2 r - 1) + 1 := by omega
    calc
      _ = 2 ^ ((Nat.clog 2 r - 1) + 1) := congrArg (2 ^ ·) h
      _ = 2 ^ (Nat.clog 2 r - 1) * 2 := Nat.pow_succ ..
      _ < 2 * r := by omega

/-- Processor that owns a block. Padding block `r+j` is handled by processor `j`. -/
def owner {r : ℕ} (hr : 0 < r) (v : Fin (2 ^ Nat.clog 2 r)) : Fin r :=
  if hv : v.val < r then ⟨v.val, hv⟩
  else ⟨v.val - r, by have := v.isLt; have := padding_lt_twice hr; omega⟩

/-- The physical blocks that a given processor must replay. -/
abbrev Owned {r : ℕ} (hr : 0 < r) (j : Fin r) :=
  {v : Fin (2 ^ Nat.clog 2 r) // owner hr v = j}

/-- At most one ordinary and one padding block reside at any processor. -/
theorem owned_card_le {r : ℕ} (hr : 0 < r) (j : Fin r) : Fintype.card (Owned hr j) ≤ 2 := by
  let extra (v : Owned hr j) : Bool := decide (r ≤ v.val.val)
  have hinj : Function.Injective extra := by
    intro a b hab
    have ha := congrArg Fin.val a.property
    have hb := congrArg Fin.val b.property
    apply Subtype.ext
    apply Fin.ext
    have hs : r ≤ a.val.val ↔ r ≤ b.val.val := by simpa only [extra, decide_eq_decide] using hab
    by_cases ha' : a.val.val < r
    · have hb' : b.val.val < r := by omega
      simpa only [owner, dite_eq_left ha', dite_eq_left hb'] using ha.trans hb.symm
    · have hb' : ¬ b.val.val < r := by omega
      simp only [owner, dite_eq_right ha', dite_eq_right hb'] at ha hb
      omega
  simpa using Fintype.card_le_of_injective extra hinj

/-- Processor-local send checks for the sort, including each extra block at its owner.
The partner and the layer number are determined by the XOR schedule. -/
def ChecksAt {r : ℕ} (hr : 0 < r) {h : ℕ} {α : Type*} [LinearOrder α]
    (sends : RAMLayout.Layer (Nat.clog 2 r) → Fin (2 ^ Nat.clog 2 r) → Wires h α)
    (x : ℕ → α) (j : Fin r) : Prop :=
  ∀ v : Owned hr j, checks v.val _ (physicalFieldsEquiv.{_,0} h (Nat.clog 2 r) α sends)
    (block h v.val.val x)

private theorem allChecks_iff {r h : ℕ} (hr : 0 < r) {α : Type*} [LinearOrder α]
    (sends : RAMLayout.Layer (Nat.clog 2 r) → Fin (2 ^ Nat.clog 2 r) → Wires h α)
    (x : ℕ → α) :
    (∀ j, ChecksAt hr sends x j) ↔
      ∀ v, checks v _ (physicalFieldsEquiv.{_,0} h (Nat.clog 2 r) α sends) (block h v.val x) :=
  ⟨fun hc v => hc (owner hr v) ⟨v, rfl⟩, fun hc _ v => hc v.val⟩

/-- For any positive team size and any input, a unique assignment of sorting link messages
passes every physical processor's checks. -/
theorem existsUnique_sends {r : ℕ} (hr : 0 < r) (h : ℕ) {α : Type*} [LinearOrder α]
    (x : ℕ → α) :
    ∃! sends : RAMLayout.Layer (Nat.clog 2 r) → Fin (2 ^ Nat.clog 2 r) → Wires h α,
      ∀ j, ChecksAt hr sends x j := by
  exact existsUnique_congr (fun s => (allChecks_iff hr s x).symm) |>.mp
    (existsUnique_physicalFields h (Nat.clog 2 r) x)

/-- The concatenated local replay outputs are exactly the ascending network's output. -/
theorem flatten_replay {r h : ℕ} (hr : 0 < r) {α : Type*} [LinearOrder α]
    (sends : RAMLayout.Layer (Nat.clog 2 r) → Fin (2 ^ Nat.clog 2 r) → Wires h α)
    (x : ℕ → α) (hc : ∀ j, ChecksAt hr sends x j) :
    (List.ofFn fun v : Fin (2 ^ Nat.clog 2 r) => List.ofFn
      (replay v _ (physicalFieldsEquiv.{_,0} h (Nat.clog 2 r) α sends) (block h v.val x))).flatten =
      List.ofFn (sort (h + Nat.clog 2 r) true (block (h + Nat.clog 2 r) 0 x)) := by
  simp_rw [replay_phases _ x ((allChecks_iff hr sends x).mp hc)]
  rw [flatten_ofFn_blocks, block_runPhases]
  rfl

/-- Testing the neighboring occupied records produced by the local replays recovers precisely
the chronological memory transcript, even for team sizes between successive powers of two. -/
theorem replayCheck_iff_transcript {r h : ℕ} (hr : 0 < r)
    {Word : Type*} [LinearOrder Word] [Zero Word]
    (sends : RAMLayout.Layer (Nat.clog 2 r) → Fin (2 ^ Nat.clog 2 r) → Wires h (TeamRecords.Slot Word))
    (x : ℕ → TeamRecords.Slot Word) (hc : ∀ j, ChecksAt hr sends x j)
    {es : List (TeamRecords.Access Word)} {rs : List (TeamRecords.Record Word)}
    (he : TeamRecords.Matches es rs) (ht : TeamRecords.Timed es)
    (hp : rs.Perm ((List.ofFn (block (h + Nat.clog 2 r) 0 x)).filterMap TeamRecords.Slot.record)) :
    TeamRecords.NeighborCheck none
      ((List.ofFn fun v : Fin (2 ^ Nat.clog 2 r) => List.ofFn (replay v _
        (physicalFieldsEquiv.{_,0} h (Nat.clog 2 r) _ sends) (block h v.val x))).flatten.filterMap
        TeamRecords.Slot.record) ↔ rs = TeamRecords.transcript (fun _ => 0) es := by
  rw [flatten_replay hr sends x hc]
  exact TeamRecords.sortedCheck_iff_transcript he ht hp

/-- A reserved bit position at a processor, indexed by its local block and its position
in the two successor fields or the send/receive pair of a cross-block layer. The sort
uses five words per padded record (one tag word and four data words). -/
abbrev BitPort {r : ℕ} (hr : 0 < r) (j : Fin r) (e w : ℕ) :=
  Owned hr j × Fin (RAMLayout.width (Nat.clog 2 r) (2 ^ e) w)

/-- Each processor reserves at most twice the per-block routing width, including the
record slots at list boundaries. There are `4 * 2^e` record positions per block. -/
theorem bitPort_card_le {r : ℕ} (hr : 0 < r) (j : Fin r) (e w : ℕ) :
    Fintype.card (BitPort hr j e w) ≤
      112 * 2 ^ e * w * ((4 * 2 ^ e * 2 ^ Nat.clog 2 r).log2) ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_fin]
  have h := Nat.mul_le_mul (owned_card_le hr j) (RAMLayout.width_le (Nat.clog 2 r) e w)
  exact h.trans_eq (by ring)

private theorem siteBits_le {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    Nat.clog 2 r + 1 ≤ TeamScales.logWidth r n := by
  have hdouble : Nat.clog 2 (2 * r) = Nat.clog 2 r + 1 := by
    rw [Nat.clog_of_two_le (by decide) (by omega), show (2 * r + 2 - 1) / 2 = r by omega]
  rw [← hdouble]
  have he : TeamScales.logWidth r n = Nat.clog 2 (2*n*r) := by
    unfold TeamScales.logWidth
    rw [← Real.natCeil_logb_natCast]
    norm_cast
  rw [he]
  exact Nat.clog_mono_right _ (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hn))

/-- For `H` RAM ticks per processor the padded sort fits in this many incident bit positions,
uniformly in the positive team size. The two initial padding operations are both included. -/
theorem bitPort_card_le_logWidth {r n H : ℕ} (hr : 0 < r) (hn : 0 < n) (hH : 0 < H)
    (j : Fin r) (w : ℕ) :
    Fintype.card (BitPort hr j (Nat.clog 2 H) w) ≤
      192 * H * w * TeamScales.logWidth r n ^ 2 := by
  let L := TeamScales.logWidth r n
  have hd : Nat.clog 2 r + 1 ≤ L := siteBits_le hr hn
  have hl : 1 ≤ L^2 := Nat.one_le_pow _ _ (by omega)
  have hc : (Nat.clog 2 r + 1).choose 2 ≤ L^2 := by
    rw [Nat.choose_two_right, pow_two]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul hd (by omega))
  have hs : 16 * w ≤ 16 * H * w * L^2 :=
    (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right 16 hH)).trans
      (Nat.le_mul_of_pos_right _ hl)
  have hb := Nat.mul_le_mul
    (Nat.mul_le_mul_right w (Nat.mul_le_mul_left 40 (padding_lt_twice hH).le)) hc
  rw [Fintype.card_prod, Fintype.card_fin, RAMLayout.width_eq]
  calc
    _ ≤ 2 * (16 * H * w * L^2 + 40 * (2*H) * w * L^2) :=
      Nat.mul_le_mul (owned_card_le hr j) (Nat.add_le_add hs hb)
    _ = _ := by dsimp [L]; ring

/-- The actual bit positions for sorter exchanges and list boundaries occupy `o(n)` bits,
uniformly for every team of at most `2^(n^ω)` processors. The exponent `D` specifies the
word length, and one choice of `ω` works for every requested constant factor `c`. -/
theorem eventually_bitPorts (D : ℕ) {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ c : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (r : ℕ) (hr : 0 < r), (r : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ ω) → ∀ j : Fin r,
      c * Fintype.card (BitPort hr j (Nat.clog 2 (TeamScales.block ξ n))
        (TeamScales.logWidth r n ^ D)) ≤ n := by
  obtain ⟨ω, hω, hsmall⟩ := TeamScales.eventually_sorting_links (D + 2) hξ
  refine ⟨ω, hω, fun c => ?_⟩
  filter_upwards [hsmall (c * 192), Filter.eventually_ge_atTop 1] with n hbudget hn
  intro r hr hmax j
  have hH : 0 < TeamScales.block ξ n := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using
      Real.one_le_rpow (by exact_mod_cast hn : 1 ≤ (n : ℝ)) (show 0 ≤ 1 - ξ / 3 by linarith)
  refine (Nat.mul_le_mul_left c (bitPort_card_le_logWidth hr hn hH j _)).trans ?_
  simpa only [pow_add, Nat.mul_assoc] using hbudget r hr hmax

section BoundaryChecks

open TeamRecords

variable {Word : Type*} [Zero Word]

/-- Predecessor scan on physical slots. A padding slot clears the predecessor. -/
def scanSlots (previous : Option (Record Word)) : List (Slot Word) → Prop
  | [] => True
  | ⟨none⟩ :: rest => scanSlots none rest
  | ⟨some r⟩ :: rest => NeighborCheck previous [r] ∧ scanSlots (some r) rest

private theorem scan_append (xs ys : List (Slot Word)) (previous : Option (Record Word)) :
    scanSlots previous (xs ++ ys) ↔
      scanSlots previous xs ∧ scanSlots ((xs.getLast?.map Slot.record).getD previous) ys := by
  induction xs generalizing previous with
  | nil => simp [scanSlots]
  | cons s ss ih =>
    rcases s with ⟨_ | r⟩ <;> rw [List.cons_append, scanSlots, scanSlots, ih] <;>
      simp [List.getLast?_cons, and_assoc]

private theorem scan_sorted [LinearOrder Word] (xs : List (Slot Word))
    (hs : xs.Pairwise (· ≤ ·)) (previous : Option (Record Word)) :
    scanSlots previous xs ↔ NeighborCheck previous (xs.filterMap Slot.record) := by
  induction xs generalizing previous with
  | nil => rfl
  | cons s ss ih =>
    obtain ⟨hh, ht⟩ := List.pairwise_cons.mp hs
    rcases s with ⟨_ | r⟩
    · have hempty : ss.filterMap Slot.record = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro r hr
        obtain ⟨⟨t⟩, ht, hrec⟩ := List.mem_filterMap.mp hr
        change t = some r at hrec
        subst t
        have bad := hh ⟨some r⟩ ht
        change Slot.code ⟨none⟩ ≤ Slot.code ⟨some r⟩ at bad
        exact (WithTop.coe_lt_top (toLex (toLex (r.address, r.tick), toLex (r.before, r.after)))).not_ge bad
      rw [scanSlots, ih ht, List.filterMap_cons_none (by rfl), hempty]
      rfl
    · simp [scanSlots, NeighborCheck, ih ht]

/-- One shared predecessor record on each boundary between successive sorted blocks. -/
abbrev Boundary (S : ℕ) (Word : Type*) := Fin (S - 1) → Option (Record Word)

omit [Zero Word] in
private def receive {S : ℕ} (initial : Option (Record Word)) (sent : Boundary S Word) :
    Fin S → Option (Record Word)
  | ⟨0, _⟩ => initial
  | ⟨k + 1, _⟩ => sent ⟨k, by omega⟩

omit [Zero Word] in
private def endSlot {B : ℕ} (hB : 0 < B) (row : Fin B → Slot Word) : Option (Record Word) :=
  (row ⟨B - 1, by omega⟩).record

omit [Zero Word] in
private def boundaryMessages {S B : ℕ} (hB : 0 < B)
    (rows : Fin S → Fin B → Slot Word) : Boundary S Word :=
  fun i => endSlot hB (rows ⟨i.val, by have := i.isLt; omega⟩)

/-- Each local validator checks the physical final slot sent to its successor, and scans
its own slots using the incoming predecessor. At the first block the predecessor is empty. -/
def BoundaryAt {S B : ℕ} (hB : 0 < B) (sent : Boundary S Word)
    (v : Fin S) (row : Fin B → Slot Word) : Prop :=
  scanSlots (receive none sent v) (List.ofFn row) ∧
    ∀ hv : v.val + 1 < S, sent ⟨v.val, by omega⟩ = endSlot hB row

private theorem scanRows {S B : ℕ} (hB : 0 < B) (rows : Fin S → Fin B → Slot Word)
    (previous : Option (Record Word)) :
    scanSlots previous (List.ofFn fun v => List.ofFn (rows v)).flatten ↔
      ∀ v, scanSlots (receive previous (boundaryMessages hB rows) v) (List.ofFn (rows v)) := by
  induction S generalizing previous with
  | zero => simp [scanSlots]
  | succ S ih =>
    let tail := fun v : Fin S => rows v.succ
    have hl : ((List.ofFn (rows 0)).getLast?.map Slot.record).getD previous =
        endSlot hB (rows 0) := by
      have hne : List.ofFn (rows 0) ≠ [] := mt List.ofFn_eq_nil_iff.mp hB.ne'
      rw [List.getLast?_eq_some_getLast hne, List.getLast_ofFn]
      rfl
    rw [List.ofFn_succ, List.flatten_cons, scan_append, hl, ih tail, Fin.forall_fin_succ]
    refine and_congr Iff.rfl (forall_congr' fun v => ?_)
    rcases v with ⟨k, hk⟩
    cases k <;> rfl

private theorem boundaryAt_iff {S B : ℕ} (hB : 0 < B) (rows : Fin S → Fin B → Slot Word)
    (sent : Boundary S Word) :
    (∀ v, BoundaryAt hB sent v (rows v)) ↔
      sent = boundaryMessages hB rows ∧ scanSlots none (List.ofFn fun v => List.ofFn (rows v)).flatten := by
  constructor
  · intro hc
    have he : sent = boundaryMessages hB rows := by
      funext i
      have hi := i.isLt
      exact (hc ⟨i.val, by omega⟩).2 (show i.val + 1 < S by omega)
    subst sent
    exact ⟨rfl, (scanRows hB rows none).mpr fun v => (hc v).1⟩
  · rintro ⟨rfl, hc⟩ v
    exact ⟨(scanRows hB rows none).mp hc v, fun _ => rfl⟩

/-- All locally accepted boundary assignments on the same blocks agree, since each
interior outgoing field is checked against its sender's final physical slot. -/
theorem boundary_ext {S B : ℕ} (hB : 0 < B) (rows : Fin S → Fin B → Slot Word)
    {sent other : Boundary S Word} (hs : ∀ v, BoundaryAt hB sent v (rows v))
    (ho : ∀ v, BoundaryAt hB other v (rows v)) : sent = other :=
  ((boundaryAt_iff hB rows sent).mp hs).1.trans ((boundaryAt_iff hB rows other).mp ho).1.symm

/-- A single boundary-record assignment passes all local checks exactly when the
claimed chronological records agree with actual RAM execution. This also covers the
singleton team whose sole block has no outgoing predecessor field. -/
theorem existsUnique_boundary_iff_transcript {r h : ℕ} (hr : 0 < r) [LinearOrder Word]
    (sends : RAMLayout.Layer (Nat.clog 2 r) → Fin (2 ^ Nat.clog 2 r) → Wires h (Slot Word))
    (x : ℕ → Slot Word) (hc : ∀ j, ChecksAt hr sends x j)
    {es : List (Access Word)} {rs : List (Record Word)}
    (he : Matches es rs) (ht : Timed es)
    (hp : rs.Perm ((List.ofFn (block (h + Nat.clog 2 r) 0 x)).filterMap Slot.record)) :
    (∃! sent : Boundary (2 ^ Nat.clog 2 r) Word, ∀ j, ∀ v : Owned hr j,
      BoundaryAt (Nat.two_pow_pos h) sent v.val (replay v.val _
        (physicalFieldsEquiv.{_,0} h (Nat.clog 2 r) _ sends) (block h v.val.val x))) ↔
      rs = transcript (fun _ => 0) es := by
  let rows := fun v : Fin (2 ^ Nat.clog 2 r) => replay v _
    (physicalFieldsEquiv.{_,0} h (Nat.clog 2 r) _ sends) (block h v.val x)
  let flat := (List.ofFn fun v => List.ofFn (rows v)).flatten
  have sorted : flat.Pairwise (· ≤ ·) := by
    dsimp only [flat, rows]
    rw [flatten_replay hr sends x hc]
    exact List.pairwise_ofFn.mpr fun _ _ hij => sort_monotone _ _ hij.le
  have hscan : scanSlots none flat ↔ rs = transcript (fun _ => 0) es :=
    (scan_sorted flat sorted none).trans (replayCheck_iff_transcript hr sends x hc he ht hp)
  have checksIff (sent : Boundary (2 ^ Nat.clog 2 r) Word) :
      (∀ j, ∀ v : Owned hr j, BoundaryAt (Nat.two_pow_pos h) sent v.val (rows v.val)) ↔
        sent = boundaryMessages (Nat.two_pow_pos h) rows ∧ scanSlots none flat :=
    (show (∀ j, ∀ v : Owned hr j, BoundaryAt (Nat.two_pow_pos h) sent v.val (rows v.val)) ↔
        ∀ v, BoundaryAt (Nat.two_pow_pos h) sent v (rows v) from
      ⟨fun hv v => hv (owner hr v) ⟨v, rfl⟩, fun hv _ v => hv v.val⟩).trans (boundaryAt_iff ..)
  constructor
  · rintro ⟨sent, hs, _⟩
    exact hscan.mp ((checksIff sent).mp hs).2
  · intro hactual
    exact ⟨boundaryMessages _ rows, (checksIff _).mpr ⟨rfl, hscan.mpr hactual⟩,
      fun sent hs => ((checksIff sent).mp hs).1⟩

end BoundaryChecks

end TeamSorting

end BorderVNP
end Computability
end OAI

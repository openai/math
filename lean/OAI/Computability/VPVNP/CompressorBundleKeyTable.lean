import OAI.Computability.VPVNP.CompressorBundleKeyMaterialization
import OAI.Computability.VPVNP.CompressorRecordsBundleKeys

/-!
# Materializing keys for every thick-wire and motif bundle

The preimage table has two consecutive sets of bundle rows. Each set has
a fixed number of live entries per row. The key table uses the same stride
as the ID table, so the rank scan reads its row and offset directly.
Successive runs of the three-probe worker share their external memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleKeys

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression

variable {w : ℕ}

/-- The four external arrays and the shape of the two sets of bundle rows. -/
structure KeyTable (w : ℕ) where
  /-- Base of the strided bundle rows containing the arc identifiers to look up. -/
  idsBase : Word w
  /-- Base of the key array addressed by arc identifier. -/
  keyBase : Word w
  /-- Base of the strided output rows receiving the gathered keys. -/
  outputBase : Word w
  /-- Base of the width array associated with the bundle key table. -/
  widthBase : Word w
  /-- Number of bundles represented in each of the thick-wire and motif row banks. -/
  bundles : ℕ
  /-- Number of words reserved per physical bundle row. -/
  stride : ℕ
  /-- Number of occupied thick-wire entries in each bundle. -/
  thickCount : ℕ
  /-- Number of occupied motif entries in each bundle. -/
  motifCount : ℕ
  /-- Size of the arc-identifier domain used to look up keys. -/
  arcCount : ℕ

/-- In each bundle, the thick-wire row and the motif row account for every
color-mask and slot-label combination exactly once. -/
theorem bundle_row_lengths_add {d c : ℕ} (hc : 2 ≤ c) :
    2 ^ c * d / 4 + PackingData.pieceCount d c = 2 ^ c * d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hc
  have h : 2 ^ (2 + k) * d = 4 * (2 ^ k * d) := by rw [pow_add]; ring
  simp only [PackingData.pieceCount, h]
  omega

/-- Both gather scans together read exactly the old physical arc count. -/
theorem bundle_rows_total (n a g : ℕ) :
    numBundles n a g * (2 ^ Shrink.colors a * 2 ^ a / 4) +
        numBundles n a g * PackingData.pieceCount (2 ^ a) (Shrink.colors a) =
      (n * 2 ^ (packingLaneBits a g)) * 2 ^ a := by
  have hc : 2 ≤ Shrink.colors a := by
    have hp := Nat.two_pow_pos a
    unfold Shrink.colors
    omega
  rw [← Nat.mul_add, bundle_row_lengths_add hc]
  simp only [numBundles, packingLaneBits, Shrink.J, Shrink.colors, pow_add]
  ring

namespace KeyTable

variable (t : KeyTable w)

/-- Thick-wire rows precede the motif rows. -/
def rowSize (b : ℕ) : ℕ := if b < t.bundles then t.thickCount else t.motifCount

/-- Natural address of the first identifier in physical row `b`. -/
def idStart (b : ℕ) : ℕ := t.idsBase.val + b * t.stride
/-- Natural address at which gathered keys for physical row `b` begin. -/
def outStart (b : ℕ) : ℕ := t.outputBase.val + b * t.stride

/-- Read the identifier at row `b`, offset `i`, then read its key from the lookup array. -/
def lookup (m : Memory w) (b i : ℕ) : Word w :=
  m (t.keyBase.val + (m (t.idStart b + i)).val)

/-- The row gather receives the base addresses of the identifier row, the key lookup, and the
output row. -/
def rowPublic (b : ℕ) : Fin 3 → Word w :=
  ![Fin.ofNat _ (t.idStart b), t.keyBase, Fin.ofNat _ (t.outStart b)]

/-- Both row tables occupy whole rectangles. The destination rectangle is
disjoint from the ID table and from both absolute-arc columns. -/
structure Layout : Prop where
  thickFits : t.thickCount ≤ t.stride
  motifFits : t.motifCount ≤ t.stride
  idsFit : t.idStart (2 * t.bundles) ≤ 2 ^ w
  outputFits : t.outStart (2 * t.bundles) ≤ 2 ^ w
  keysFit : t.keyBase.val + t.arcCount ≤ 2 ^ w
  idsApart : t.idStart (2 * t.bundles) ≤ t.outputBase.val ∨
    t.outStart (2 * t.bundles) ≤ t.idsBase.val
  keysApart : t.keyBase.val + t.arcCount ≤ t.outputBase.val ∨
    t.outStart (2 * t.bundles) ≤ t.keyBase.val
  widthsApart : t.widthBase.val + t.arcCount ≤ t.outputBase.val ∨
    t.outStart (2 * t.bundles) ≤ t.widthBase.val

theorem size_le_stride (reg : t.Layout) (b : ℕ) : t.rowSize b ≤ t.stride := by
  unfold rowSize
  split <;> first | exact reg.thickFits | exact reg.motifFits

private theorem rowBounds (reg : t.Layout) (b : ℕ) (hb : b < 2 * t.bundles) :
    t.idStart b + t.rowSize b ≤ t.idStart (2 * t.bundles) ∧
    t.outStart b + t.rowSize b ≤ t.outStart (2 * t.bundles) := by
  have h := Nat.mul_le_mul_right t.stride (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at h
  have hs := t.size_le_stride reg b
  dsimp [idStart, outStart]
  omega

/-- The word address used by the rank worker agrees with the rectangular
natural address for every slot, including the padding. -/
theorem outAddress_eq (reg : t.Layout) (b stride offset : Word w)
    (hb : b.val < 2 * t.bundles) (hs : stride.val = t.stride) (hi : offset.val < t.stride) :
    (t.outputBase + b * stride + offset).val = t.outStart b.val + offset.val := by
  have fit := reg.outputFits
  have bound := Nat.mul_le_mul_right t.stride (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at bound
  dsimp [outStart] at fit ⊢
  rw [Fin.val_add, Fin.val_add, Fin.val_mul, hs, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega)]

private theorem public_eq (reg : t.Layout) (b : ℕ) (hb : b < 2 * t.bundles) :
    ((t.rowPublic b) 0).val = t.idStart b ∧ ((t.rowPublic b) 2).val = t.outStart b := by
  have idFit := reg.idsFit
  have outFit := reg.outputFits
  have h := Nat.mul_le_mul_right t.stride (Nat.succ_le_of_lt hb)
  rw [Nat.succ_mul] at h
  change (t.idStart b) % (2 ^ w) = _ ∧ (t.outStart b) % (2 ^ w) = _
  by_cases hzero : t.stride = 0
  · simp [idStart, outStart, hzero, Nat.mod_eq_of_lt t.idsBase.isLt, Nat.mod_eq_of_lt t.outputBase.isLt]
  · dsimp [idStart, outStart] at idFit outFit ⊢
    exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩

theorem rowRegions (reg : t.Layout) (b : ℕ) (hb : b < 2 * t.bundles) :
    KeyRowRegions (t.rowPublic b) (t.rowSize b) t.arcCount t.widthBase.val := by
  obtain ⟨hid, hout⟩ := t.public_eq reg b hb
  obtain ⟨ib, ob⟩ := t.rowBounds reg b hb
  have is : t.idsBase.val ≤ t.idStart b := Nat.le_add_right ..
  have os : t.outputBase.val ≤ t.outStart b := Nat.le_add_right ..
  have key : (t.rowPublic b) 1 = t.keyBase := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hid]
    exact ib.trans reg.idsFit
  · simpa only [key] using reg.keysFit
  · rw [hout]
    exact ob.trans reg.outputFits
  · rw [hid, hout]
    have := reg.idsApart
    omega
  · rw [key, hout]
    have := reg.keysApart
    omega
  · rw [hout]
    have := reg.widthsApart
    omega

/-- Each row scan uses the memory left by all preceding rows. Its exact
cost, persistent cursor, readback, and external frame are recorded. -/
inductive Runs (initial : Memory w) : ℕ → List (Report w) → Prop where
  | nil : Runs initial 0 []
  | snoc {b earlier reports} (previous : Runs initial b earlier)
      (row : let mem := after initial (eventLog earlier)
             let p := t.rowPublic b
             SlotOwners.FilledRun ((template materializeKey 0).instantiate w p).program
               13 3 12 (t.rowSize b) (p 2) (t.lookup mem b) mem reports) :
      Runs initial (b + 1) (earlier ++ reports)

/-- Exactly the live prefixes of the completed rows have been written. The
frame also covers every unused padding cell inside a completed row. -/
structure Completed (initial final : Memory w) (k : ℕ) : Prop where
  filled : ∀ b < k, ∀ i < t.rowSize b, final (t.outStart b + i) = t.lookup initial b i
  frame : ∀ addr, (∀ b < k, addr < t.outStart b ∨ t.outStart b + t.rowSize b ≤ addr) →
    final addr = initial addr

theorem Completed.outside {initial final : Memory w} {k : ℕ}
    (done : t.Completed initial final k) (reg : t.Layout) (hk : k ≤ 2 * t.bundles)
    (addr : ℕ) (h : addr < t.outputBase.val ∨ t.outStart (2 * t.bundles) ≤ addr) :
    final addr = initial addr := by
  apply done.frame
  intro b hb
  have ob := (t.rowBounds reg b (hb.trans_le hk)).2
  have os : t.outputBase.val ≤ t.outStart b := Nat.le_add_right ..
  omega

/-- Throughout a prefix of the scan all cells of the ID, classifier-key,
and old-width inputs retain their original values. -/
theorem Completed.inputs {initial final : Memory w} {k : ℕ}
    (done : t.Completed initial final k) (reg : t.Layout) (hk : k ≤ 2 * t.bundles) :
    (∀ j < 2 * t.bundles * t.stride, final (t.idsBase.val + j) = initial (t.idsBase.val + j)) ∧
    (∀ e < t.arcCount, final (t.keyBase.val + e) = initial (t.keyBase.val + e)) ∧
    (∀ e < t.arcCount, final (t.widthBase.val + e) = initial (t.widthBase.val + e)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    apply done.outside t reg hk
    have := reg.idsApart
    dsimp [idStart] at this
    omega
  · intro e he
    apply done.outside t reg hk
    have := reg.keysApart
    omega
  · intro e he
    apply done.outside t reg hk
    have := reg.widthsApart
    omega

/-- Number of actual ID entries in the first `k` rows. -/
def entries (k : ℕ) := min k t.bundles * t.thickCount + (k - t.bundles) * t.motifCount

private theorem entries_succ (k : ℕ) : t.entries (k + 1) = t.entries k + t.rowSize k := by
  by_cases h : k < t.bundles
  · simp [entries, rowSize, h, Nat.min_eq_left h.le,
      Nat.sub_eq_zero_of_le h.le, Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt h), Nat.succ_mul]
  · have he : k + 1 - t.bundles = (k - t.bundles) + 1 := by omega
    simp [entries, rowSize, h, Nat.min_eq_right (by omega : t.bundles ≤ k),
      Nat.min_eq_right (by omega : t.bundles ≤ k + 1), he, Nat.succ_mul, Nat.add_assoc]

/-- Materialize any prefix of the two rectangular tables in ordinal bucket
order, accounting for the shorter real prefixes of thick-wire rows. -/
theorem runPrefix (reg : t.Layout) (initial : Memory w)
    (legal : ∀ b < 2 * t.bundles, ∀ i < t.rowSize b, (initial (t.idStart b + i)).val < t.arcCount)
    (k : ℕ) (hk : k ≤ 2 * t.bundles) :
    ∃ reports, t.Runs initial k reports ∧ t.Completed initial (after initial (eventLog reports)) k ∧
      RAMBuckets.cost Report.probes reports = 4 * t.entries k := by
  induction k with
  | zero => exact ⟨[], .nil, ⟨by simp, fun _ _ => rfl⟩, by simp [RAMBuckets.cost, entries]⟩
  | succ b ih =>
    obtain ⟨earlier, runs, done, cost⟩ := ih (by omega)
    let mem := after initial (eventLog earlier)
    let p := t.rowPublic b
    have hb : b < 2 * t.bundles := hk
    obtain ⟨hid, hout⟩ := t.public_eq reg b hb
    have hkey : p 1 = t.keyBase := rfl
    obtain ⟨ids, keys, _⟩ := done.inputs t reg (by omega)
    have sameId (i : ℕ) (hi : i < t.rowSize b) : mem (t.idStart b + i) = initial (t.idStart b + i) := by
      have ib := (t.rowBounds reg b hb).1
      dsimp [idStart] at ib ⊢
      rw [Nat.add_assoc]
      exact ids _ (by omega)
    have sameValue (i : ℕ) (hi : i < t.rowSize b) : t.lookup mem b i = t.lookup initial b i := by
      rw [lookup, lookup, sameId i hi]
      exact keys _ (legal b hb i hi)
    obtain ⟨reports, row, _⟩ := materialize_run p mem (t.rowSize b) t.arcCount t.widthBase.val
      (t.rowRegions reg b hb) (fun i hi => by
        change (mem (((t.rowPublic b) 0).val + i)).val < _
        rw [hid, sameId i hi]
        exact legal b hb i hi)
    have recorded : SlotOwners.FilledRun ((template materializeKey 0).instantiate w p).program
        13 3 12 (t.rowSize b) (p 2) (t.lookup mem b) mem reports := by
      convert row using 1
      dsimp [lookup, p]
      rw [hid]
      rfl
    have afterBoth : after initial (eventLog (earlier ++ reports)) = after mem (eventLog reports) := by
      simp only [eventLog, List.flatMap_append, after, List.foldl_append, mem]
    refine ⟨earlier ++ reports, .snoc runs recorded, ?_, ?_⟩
    · rw [afterBoth]
      constructor
      · intro a ha i hi
        by_cases eq : a = b
        · subst a
          have h := recorded.filled i hi
          change after mem (eventLog reports) (((t.rowPublic b) 2).val + i) = t.lookup mem b i at h
          rw [hout] at h
          exact h.trans (sameValue i hi)
        · have hab : a < b := by omega
          have bound := Nat.mul_le_mul_right t.stride (Nat.succ_le_of_lt hab)
          rw [Nat.succ_mul] at bound
          have hs := t.size_le_stride reg a
          have keep := recorded.frame (t.outStart a + i) (Or.inl (by
            change _ < ((t.rowPublic b) 2).val
            rw [hout]
            dsimp [outStart]
            omega))
          exact keep.trans (done.filled a hab i hi)
      · intro addr outside
        have right := outside b (Nat.lt_succ_self b)
        have localFrame := recorded.frame addr (by
          change addr < ((t.rowPublic b) 2).val ∨ ((t.rowPublic b) 2).val + t.rowSize b ≤ addr
          rwa [hout])
        exact localFrame.trans (done.frame addr fun a ha => outside a (Nat.lt_succ_of_lt ha))
    · rw [RAMBuckets.cost_append, cost, recorded.cost, entries_succ, Nat.mul_add]

/-- The whole pair of tables in ordinal order, with exactly four charged
operations per real entry across both kinds of bundles. -/
theorem run (reg : t.Layout) (initial : Memory w)
    (legal : ∀ b < 2 * t.bundles, ∀ i < t.rowSize b, (initial (t.idStart b + i)).val < t.arcCount) :
    ∃ reports, t.Runs initial (2 * t.bundles) reports ∧
      t.Completed initial (after initial (eventLog reports)) (2 * t.bundles) ∧
      RAMBuckets.cost Report.probes reports = 4 * (t.bundles * (t.thickCount + t.motifCount)) := by
  have h : t.entries (2 * t.bundles) = t.bundles * (t.thickCount + t.motifCount) := by
    rw [entries, Nat.min_eq_right (by omega), show 2 * t.bundles - t.bundles = t.bundles by omega,
      Nat.mul_add]
  simpa only [h] using t.runPrefix reg initial legal (2 * t.bundles) (le_refl _)

/-- Instantiate the row counts for the dyadic packing with `n` base sites,
degree `2^a`, and `g` residual lane bits. -/
def dyadic (ids keys output widths : Word w) (stride n a g : ℕ) : KeyTable w where
  idsBase := ids
  keyBase := keys
  outputBase := output
  widthBase := widths
  bundles := numBundles n a g
  stride := stride
  thickCount := 2 ^ Shrink.colors a * 2 ^ a / 4
  motifCount := PackingData.pieceCount (2 ^ a) (Shrink.colors a)
  arcCount := (n * 2 ^ packingLaneBits a g) * 2 ^ a

/-- For the packing's actual two row counts the full materialization costs
exactly four charged operations per original arc. -/
theorem dyadic_run (ids keys output widths : Word w) (stride n a g : ℕ) (initial : Memory w)
    (reg : (dyadic ids keys output widths stride n a g).Layout)
    (legal : let t := dyadic ids keys output widths stride n a g
             ∀ b < 2 * t.bundles, ∀ i < t.rowSize b, (initial (t.idStart b + i)).val < t.arcCount) :
    let t := dyadic ids keys output widths stride n a g
    ∃ reports, t.Runs initial (2 * t.bundles) reports ∧
      t.Completed initial (after initial (eventLog reports)) (2 * t.bundles) ∧
      RAMBuckets.cost Report.probes reports = 4 * t.arcCount := by
  let t := dyadic ids keys output widths stride n a g
  have counted : t.bundles * (t.thickCount + t.motifCount) = t.arcCount := by
    rw [Nat.mul_add]
    exact bundle_rows_total n a g
  simpa only [counted] using t.run reg initial legal

end KeyTable

end CompressorRecords.BundleKeys

end VPVNP
end Computability
end OAI

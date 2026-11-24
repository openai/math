import OAI.Computability.VPVNP.CompressorBundleFixedGatherTable
import OAI.Computability.VPVNP.CompressorRecordsBundleGather

/-!
# Typed readback of the complete rectangular bundle key table

The ID rows in the post-memory of the native append pass supply the addresses
for the complete key-gathering schedule. Every live cell of the resulting
rectangle contains the key of the corresponding thick wire or motif. The
whole schedule costs four calls-plus-probes per original arc.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather

open Compression Compression.PackingData BurstRAM BundleLists BundleRank BundleKeys

variable {V H Tag L : Type} {n d c A w N J : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable (arcs : Arc V H Tag L d c ≃ Fin A) (site : Site V Tag L ≃ Fin n)

/-- Specialize the rectangular key table to the row stride and ID base
written by the preimage pass. -/
def table (A n d c : ℕ) (p : Fin 6 → Word w) (keys out widths : Word w) : KeyTable w where
  idsBase := p 5
  keyBase := keys
  outputBase := out
  widthBase := widths
  bundles := n*d
  stride := (p 4).val
  thickCount := 2^c*d/4
  motifCount := pieceCount d c
  arcCount := A

/-- The mathematical ID rows held in the physical count and row arrays. -/
def Stored (p : Fin 6 → Word w) (mem : Memory w) : Prop :=
  ∀ b : Bucket V Tag L d, let u := Fin.ofNat (2^w) (bucketIndex site b).val
    rowRepresents mem (countAt p u) (rowAt p u) (arcList P arcs site b)

omit [AddCommGroup Tag] [AddCommGroup L] in
private theorem size_index (p : Fin 6 → Word w) (keys out widths : Word w) (b : Bucket V Tag L d) :
    (table A n d c p keys out widths).rowSize (bucketIndex site b).val = rowLength (c := c) b := by
  cases b with
  | inl b =>
    change (if (portIndex site b).val < n*d then _ else _) = _
    rw [ite_eq_left (portIndex site b).isLt]; rfl
  | inr b =>
    change (if n*d+(portIndex site b).val < n*d then _ else _) = _
    rw [ite_eq_right (by omega)]; rfl

variable (p : Fin 6 → Word w) (keys out widths : Word w)
local notation "T" => table A n d c p keys out widths

omit [AddCommGroup Tag] [AddCommGroup L] in
private theorem idStart_eq (reg : (T).Layout) (hn : n*d+n*d ≤ 2^w) (b : Bucket V Tag L d) :
    (T).idStart (bucketIndex site b).val = (rowAt p (Fin.ofNat _ (bucketIndex site b).val)).val := by
  let i := (bucketIndex site b).val
  have hi : i < n*d+n*d := (bucketIndex site b).isLt
  have fit := reg.idsFit
  change (p 5).val + (2*(n*d))*(p 4).val ≤ 2^w at fit
  change (p 5).val + i*(p 4).val = (p 5+Fin.ofNat (2^w) i * p 4).val
  rw [Fin.val_add, Fin.val_mul, Fin.val_ofNat, Nat.mod_eq_of_lt (hi.trans_le hn), Nat.add_mod_mod]
  by_cases hs : (p 4).val = 0
  · simp [hs, Nat.mod_eq_of_lt (p 5).isLt]
  · have h := Nat.mul_le_mul_right (p 4).val (show i+1 ≤ 2*(n*d) by omega)
    rw [Nat.succ_mul] at h
    exact (Nat.mod_eq_of_lt (by omega)).symm

private theorem id_at (reg : (T).Layout) (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w)
    (b : Bucket V Tag L d) (mem : Memory w) (stored : Stored P arcs site p mem)
    (i : Fin (arcList (w := w) P arcs site b).length) :
    (mem ((T).idStart (bucketIndex site b).val+i.val)).val = (arcs (ordinalEquiv P arcs site hA hn b i).val).val := by
  rw [idStart_eq site p keys out widths reg hn b, (stored b).2 i]
  change ((arcList P arcs site b).get i).val = _
  rw [ordinalEquiv_id P arcs site hA hn, Fin.val_ofNat, Nat.mod_eq_of_lt ((arcs _).isLt.trans_le hA)]

include P arcs site in
omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] in
private theorem total_arcs (hc : 2 ≤ c) : (n*d)*(2^c*d/4 + pieceCount d c) = A := by
  let f : Arc V H Tag L d c ≃ Fin ((n*d)*(2^c*d)) :=
    ((portIndex site).prodCongr (((bitWordFinEquiv c).prodCongr P.slotLabel).trans finProdFinEquiv)).trans finProdFinEquiv
  have e : (n*d)*(2^c*d) = A := by simpa using Fintype.card_congr (f.symm.trans arcs)
  rw [← e]
  congr 1
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hc
  unfold pieceCount
  rw [pow_add, show 2^2 = 4 by decide, Nat.mul_assoc]
  omega

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Physical table readback directly in terms of the original typed arcs. -/
def KeyRows (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (initial final : Memory w) : Prop :=
  ∀ (b : Bucket V Tag L d) (i : Fin (arcList (w := w) P arcs site b).length),
    final ((T).outStart (bucketIndex site b).val+i.val) =
      initial (keys.val+(arcs (ordinalEquiv P arcs site hA hn b i).val).val)

private theorem size_arcList (hc : 2 ≤ c) (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w)
    (b : Bucket V Tag L d) :
    (T).rowSize (bucketIndex site b).val = (arcList (w := w) P arcs site b).length :=
  (size_index site p keys out widths b).trans (arcList_length P arcs site hc hA hn b).symm

private theorem table_legal (hc : 2 ≤ c) (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (reg : (T).Layout)
    (initial : Memory w) (stored : Stored P arcs site p initial) (j : ℕ) (hj : j < 2*(T).bundles)
    (i : ℕ) (hi : i < (T).rowSize j) :
    (initial ((T).idStart j+i)).val < (T).arcCount := by
  have size := size_arcList P arcs site p keys out widths hc hA hn
  change j < 2*(n*d) at hj
  obtain ⟨b,hb⟩ := (bucketIndex site (d := d)).surjective ⟨j,by omega⟩
  have he : (bucketIndex site b).val = j := congrArg Fin.val hb
  let k : Fin (arcList (w := w) P arcs site b).length := ⟨i, by rwa [← size b, he]⟩
  exact he ▸ (id_at P arcs site p keys out widths reg hA hn b initial stored k).trans_lt (arcs _).isLt

private theorem keyRows_completed (hc : 2 ≤ c) (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (reg : (T).Layout)
    (initial final : Memory w) (stored : Stored P arcs site p initial)
    (done : (T).Completed initial final (2*(T).bundles)) :
    KeyRows P arcs site p keys out widths hA hn initial final := by
  intro b i
  have size := size_arcList P arcs site p keys out widths hc hA hn
  have hb := (bucketIndex site b).isLt
  have h := done.filled (bucketIndex site b).val (show _ < 2*(n*d) by omega) i.val ((size b).symm ▸ i.isLt)
  rw [KeyTable.lookup, id_at P arcs site p keys out widths reg hA hn b initial stored i] at h
  exact h

/-- Run the key table over the actual list memory and recover every typed
entry, with the exact original-arc cost. `Completed.frame` covers every
cell outside the written prefixes, including the original widths. -/
theorem gather_table (hc : 2 ≤ c) (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w) (reg : (T).Layout)
    (initial : Memory w) (stored : Stored P arcs site p initial) :
    ∃ rs, (T).Runs initial (2*(T).bundles) rs ∧ (T).Completed initial (after initial (eventLog rs)) (2*(T).bundles) ∧
      KeyRows P arcs site p keys out widths hA hn initial (after initial (eventLog rs)) ∧
      RAMBuckets.cost Report.probes rs = 4*A := by
  obtain ⟨rs,run,done,cost⟩ := (T).run reg initial (table_legal P arcs site p keys out widths hc hA hn reg initial stored)
  exact ⟨rs,run,done,keyRows_completed P arcs site p keys out widths hc hA hn reg initial _ stored done,
    cost.trans (congrArg (4*·) (total_arcs P arcs site hc))⟩

/-- A single public bank supplies the cursor decoder and all three bases
for the entire gather. Its report sequence has the exact same physical
readback and cost as the row-wise schedule. -/
theorem fixed_gather_table (hc : 2 ≤ c) (hA : A < 2^w) (hn : n*d+n*d ≤ 2^w) (reg : (T).Layout)
    (initial : Memory w) (stored : Stored P arcs site p initial) :
    ∃ rs, Fixed.FullRun (Fixed.parameters T) initial (Fixed.slot T reg) rs ∧
      (T).Completed initial (after initial (eventLog rs)) (2*(T).bundles) ∧
      KeyRows P arcs site p keys out widths hA.le hn initial (after initial (eventLog rs)) ∧
      RAMBuckets.cost Report.probes rs = 4*A := by
  have count : Fixed.entryCount T = A := total_arcs P arcs site hc
  obtain ⟨rs,run,done⟩ := Fixed.table_run T reg (count ▸ hA) initial
    (table_legal P arcs site p keys out widths hc hA.le hn reg initial stored)
  exact ⟨rs,run,done,keyRows_completed P arcs site p keys out widths hc hA.le hn reg initial _ stored done,
    run.cost.trans (congrArg (4*·) count)⟩

end CompressorRecords.BundleGather

end VPVNP
end Computability
end OAI

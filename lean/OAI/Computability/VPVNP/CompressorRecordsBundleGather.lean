import OAI.Computability.VPVNP.CompressorRecordsBundleLists
import OAI.Computability.VPVNP.CompressorRecordsBundleRank
import OAI.Computability.VPVNP.CompressorBundleKeyMaterialization

/-!
# Recovering the two bundle numberings from the classified arc directory

The preimage pass stores original arc IDs. To rank one of them, gather the
keys at those IDs into a consecutive row and run the native rank scan on the
row. Both steps use the same actual arc order, including distinct parallel
arcs. Their order in memory can differ from their order by relative key.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather

open Compression Compression.PackingData BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open BundleLists Slots BundleRank

variable {V H Tag L : Type} {A n d c w N J : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable (arcs : Arc V H Tag L d c ≃ Fin A) (site : Site V Tag L ≃ Fin n)
variable (hA : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w)

private def incident {E S : Type*} {m : ℕ} {port : E → S} {b : S}
    (order : Fin m ≃ {e // port e = b}) : IncidentRow port b where
  ids := List.ofFn fun i ↦ (order i).val
  nodup := List.nodup_ofFn_ofInjective (Subtype.val_injective.comp order.injective)
  complete e := by
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩; exact (order i).prop
    · intro he; exact ⟨order.symm ⟨e,he⟩,congrArg Subtype.val (order.apply_symm_apply _)⟩

/-- The typed thick row is in the actual ID order used by the append scan. -/
def thickRow (b : Port V Tag L d) : IncidentRow (fun a : P.ThickWire ↦ a.val.1) b :=
  incident ((ordinalEquiv P arcs site hA hn (.inl b)).trans (thickEquiv P b))

/-- The typed motif row has the same indices as the native row of original IDs. -/
def motifRow (b : Port V Tag L d) : IncidentRow P.bundle b :=
  incident ((ordinalEquiv P arcs site hA hn (.inr b)).trans (motifEquiv P b))

/-- A successful native key scan on this bundle, together with the untouched
old width column. Its report sequence includes all addresses and costs. -/
structure Gathered (g : Fin 3 → Word w) (count arcCount widthBase : ℕ)
    (mem : Memory w) (rs : List (Report w)) : Prop where
  run : SlotOwners.FilledRun ((template BundleKeys.materializeKey 0).instantiate w g).program
    13 3 12 count (g 2) (fun i ↦ mem ((g 1).val + (mem ((g 0).val+i)).val)) mem rs
  widths : ∀ e < arcCount, after mem (eventLog rs) (widthBase+e) = mem (widthBase+e)

/-- From the actual memory of the preimage pass, gather keys by indirect lookup.
Every returned position now addresses the classifier's key for its typed arc. -/
theorem gather (p : Fin 6 → Word w) (hp : (p 2).val = n*d+n*d) (b : Bucket V Tag L d)
    (mem : Memory w) (filled : PreimagesAt p (wordOwner P arcs site) mem A)
    (g : Fin 3 → Word w) (src : g 0 = rowAt p (Fin.ofNat _ (bucketIndex site b).val))
    (widthBase : ℕ)
    (reg : BundleKeys.KeyRowRegions g (arcList (w := w) P arcs site b).length A widthBase) :
    ∃ rs, Gathered g (arcList (w := w) P arcs site b).length A widthBase mem rs ∧
      ∀ i : Fin (arcList (w := w) P arcs site b).length,
        after mem (eventLog rs) ((g 2).val+i.val) =
          mem ((g 1).val+(arcs (ordinalEquiv P arcs site hA hn b i).val).val) := by
  let u := Fin.ofNat (2^w) (bucketIndex site b).val
  have hu : u < p 2 := by
    change (bucketIndex site b).val % (2^w) < (p 2).val
    rw [Nat.mod_eq_of_lt ((bucketIndex site b).isLt.trans_le hn), hp]
    exact (bucketIndex site b).isLt
  have hids (i : Fin (arcList (w := w) P arcs site b).length) :
      (mem ((g 0).val+i.val)).val = (arcs (ordinalEquiv P arcs site hA hn b i).val).val := by
    rw [src, (filled.rows u hu).2 i]
    change ((arcList P arcs site b).get i).val = _
    rw [ordinalEquiv_id P arcs site hA hn, Fin.val_ofNat,
      Nat.mod_eq_of_lt ((arcs _).isLt.trans_le hA)]
  obtain ⟨rs, run, widths⟩ := BundleKeys.materialize_run g mem (arcList P arcs site b).length A
    widthBase reg (fun i hi ↦ (hids ⟨i,hi⟩).trans_lt (arcs _).isLt)
  refine ⟨rs, ⟨run,widths⟩, fun i ↦ ?_⟩
  rw [run.filled i.val i.isLt, hids i]

/-- Materialized row addresses correspond one-for-one to old thick wires.
The classifier column can be populated anywhere disjoint from the destination. -/
theorem thick_read (b : Port V Tag L d) (mem out : Memory w) (g : Fin 3 → Word w)
    (hf : 2^c*d ≤ 2^w)
    (keys : ∀ a : P.ThickWire, mem ((g 1).val+(arcs a.val).val) = (thickKey P a).castLE hf)
    (copy : ∀ i : Fin (arcList (w := w) P arcs site (.inl b)).length,
      out ((g 2).val+i.val) = mem ((g 1).val+(arcs (ordinalEquiv P arcs site hA hn (.inl b) i).val).val)) :
    let r := thickRow P arcs site hA hn b
    ∀ i : Fin r.ids.length, out ((g 2).val+i.val) = (thickKey P r.ids[i.val]).castLE hf := by
  intro r i
  let j : Fin (arcList (w := w) P arcs site (.inl b)).length :=
    ⟨i.val, by simpa [r,thickRow,incident] using i.isLt⟩
  have he : r.ids[i.val] = (thickEquiv P b (ordinalEquiv P arcs site hA hn (.inl b) j)).val := by
    simp [r,thickRow,incident,j]
  rw [he, copy j]
  exact keys (thickEquiv P b (ordinalEquiv P arcs site hA hn (.inl b) j)).val

theorem motif_read (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (b : Port V Tag L d)
    (mem out : Memory w) (g : Fin 3 → Word w) (hf : N*(J*(d*(2^c*d))) ≤ 2^w)
    (keys : ∀ m : P.Motif, mem ((g 1).val+(arcs m.val).val) = (motifKey P vertices tags m).castLE hf)
    (copy : ∀ i : Fin (arcList (w := w) P arcs site (.inr b)).length,
      out ((g 2).val+i.val) = mem ((g 1).val+(arcs (ordinalEquiv P arcs site hA hn (.inr b) i).val).val)) :
    let r := motifRow P arcs site hA hn b
    ∀ i : Fin r.ids.length, out ((g 2).val+i.val) = (motifKey P vertices tags r.ids[i.val]).castLE hf := by
  intro r i
  let j : Fin (arcList (w := w) P arcs site (.inr b)).length :=
    ⟨i.val, by simpa [r,motifRow,incident] using i.isLt⟩
  have he : r.ids[i.val] = (motifEquiv P b (ordinalEquiv P arcs site hA hn (.inr b) j)).val := by
    simp [r,motifRow,incident,j]
  rw [he, copy j]
  exact keys (motifEquiv P b (ordinalEquiv P arcs site hA hn (.inr b) j)).val

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Gather an actual DD row from the classified directory. Starting in that
post-memory, ranking any of its members writes its concatenation number. -/
theorem gather_rank_thick (hc : 2 ≤ c) (p : Fin 6 → Word w) (hp : (p 2).val = n*d+n*d)
    (b : Port V Tag L d) (mem : Memory w) (filled : PreimagesAt p (wordOwner P arcs site) mem A)
    (g : Fin 3 → Word w) (src : g 0 = rowAt p (Fin.ofNat _ (bucketIndex site (.inl b)).val))
    (widthBase : ℕ) (reg : BundleKeys.KeyRowRegions g (2^c*d/4) A widthBase)
    (hf : 2^c*d < 2^w)
    (keys : ∀ a : P.ThickWire, mem ((g 1).val+(arcs a.val).val) = (thickKey P a).castLE hf.le) :
    ∃ rs, Gathered g (2^c*d/4) A widthBase mem rs ∧
      ∀ (x : P.ThickFiber b) (dst : Word w),
        RankWrite (2^c*d/4) ![g 2,dst] (after mem (eventLog rs)) ((thickKey P x.val).castLE hf.le)
          (Fin.ofNat _ (P.sortedThickNumbering hc b x).val) := by
  have hA : A ≤ 2^w := by have := reg.keysFit; omega
  have hn : n*d+n*d ≤ 2^w := hp ▸ (p 2).isLt.le
  have hlen := arcList_length P arcs site hc hA hn (.inl b)
  change (arcList P arcs site (.inl b)).length = 2^c*d/4 at hlen
  obtain ⟨rs,run,copy⟩ := gather P arcs site hA hn p hp (.inl b) mem filled g src widthBase (hlen ▸ reg)
  refine ⟨rs, hlen ▸ run, fun x dst ↦ ?_⟩
  exact thick_rank_native P hc hf b (thickRow P arcs site hA hn b) x ![g 2,dst] _
    (thick_read P arcs site hA hn b mem _ g hf.le keys copy) reg.destinationFits

/-- Gather the actual CD row and rank a member to obtain its AB piece number
in the sorted bundle numbering. -/
theorem gather_rank_motif (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (hc : 2 ≤ c)
    (p : Fin 6 → Word w) (hp : (p 2).val = n*d+n*d) (b : Port V Tag L d)
    (mem : Memory w) (filled : PreimagesAt p (wordOwner P arcs site) mem A)
    (g : Fin 3 → Word w) (src : g 0 = rowAt p (Fin.ofNat _ (bucketIndex site (.inr b)).val))
    (widthBase : ℕ) (reg : BundleKeys.KeyRowRegions g (pieceCount d c) A widthBase)
    (hf : N*(J*(d*(2^c*d))) < 2^w)
    (keys : ∀ m : P.Motif, mem ((g 1).val+(arcs m.val).val) = (motifKey P vertices tags m).castLE hf.le) :
    ∃ rs, Gathered g (pieceCount d c) A widthBase mem rs ∧
      ∀ (x : P.MotifFiber b) (dst : Word w),
        RankWrite (pieceCount d c) ![g 2,dst] (after mem (eventLog rs)) ((motifKey P vertices tags x.val).castLE hf.le)
          (Fin.ofNat _ (P.sortedBundleNumbering vertices tags hc b x).val) := by
  have hA : A ≤ 2^w := by have := reg.keysFit; omega
  have hn : n*d+n*d ≤ 2^w := hp ▸ (p 2).isLt.le
  have hlen := arcList_length P arcs site hc hA hn (.inr b)
  change (arcList P arcs site (.inr b)).length = pieceCount d c at hlen
  obtain ⟨rs,run,copy⟩ := gather P arcs site hA hn p hp (.inr b) mem filled g src widthBase (hlen ▸ reg)
  refine ⟨rs, hlen ▸ run, fun x dst ↦ ?_⟩
  exact motif_rank_native P vertices tags hc hf b (motifRow P arcs site hA hn b) x ![g 2,dst] _
    (motif_read P arcs site hA hn vertices tags b mem _ g hf.le keys copy) reg.destinationFits

end CompressorRecords.BundleGather

end VPVNP
end Computability
end OAI

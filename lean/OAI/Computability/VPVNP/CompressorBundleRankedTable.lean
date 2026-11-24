import OAI.Computability.VPVNP.CompressorBundleRankLayout

/-!
# Ranking all old ports from the completed bundle lists

The native gather schedule runs on the append pass's memory. The rank
scan starts in the resulting memory, uses the same owner and count cells,
and writes the sorted bundle number for every original arc. No input about
the contents of the unused tail of a thick-wire row is required.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.PackingData
open BundleLists BundleRank BundleKeys PortRankRAM

variable {V H Tag L : Type} {n d c A w N J : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable (arcs : Arc V H Tag L d c ≃ Fin A) (site : Site V Tag L ≃ Fin n)
variable (p : Fin 6 → Word w) (keys out widths dest : Word w)
local notation "T" => table A n d c p keys out widths
local notation "R" => rankPublic p keys out dest

private theorem owner_preserved (reg : (T).Layout) (sep : RankLayout p keys out dest A (2*(n*d)))
    (pre : RowRegions p) (hA : (p 0).val = A) {m f : Memory w}
    (done : (T).Completed m f (2*(n*d))) (i : Word w) (hi : i.val < A) :
    ownerAt p f i = ownerAt p m i := by
  have fit := pre.ownersBeforeCounts
  unfold ownerAt
  rw [Fin.val_add,Nat.mod_eq_of_lt (by have := (p 3).isLt; omega)]
  exact done.outside T reg (le_refl _) _ (sep.keepOwners.outside hi)

private theorem count_preserved (reg : (T).Layout) (sep : RankLayout p keys out dest A (2*(n*d)))
    (pre : RowRegions p) (hB : (p 2).val = n*d+n*d) {m f : Memory w}
    (done : (T).Completed m f (2*(n*d))) (u : Word w) (hu : u.val < 2*(n*d)) :
    f (countAt p u).val = m (countAt p u).val := by
  have fit := pre.countsBeforeRows
  rw [countAt,Fin.val_add,Nat.mod_eq_of_lt (by have := (p 5).isLt; omega)]
  exact done.outside T reg (le_refl _) _ (sep.keepCounts.outside hu)

private theorem ranked_header (reg : (T).Layout) (sep : RankLayout p keys out dest A (2*(n*d)))
    (pre : RowRegions p) (hA : (p 0).val = A) (hB : (p 2).val = n*d+n*d)
    {m f : Memory w} (done : (T).Completed m f (2*(n*d)))
    (filled : PreimagesAt p (wordOwner P arcs site) m A) (a : Arc V H Tag L d c)
    (b : Bucket V Tag L d) (hb : bucketOf P a = b) :
    let i := Fin.ofNat (2^w) (arcs a).val
    (lengthAt R f i).val = (arcList (w := w) P arcs site b).length ∧
      (start R f i).val = (T).outStart (bucketIndex site b).val ∧
      pivot R f i = m (keys.val+(arcs a).val) := by
  intro i
  let u := Fin.ofNat (2^w) (bucketIndex site b).val
  have ha : A ≤ 2^w := hA ▸ (p 0).isLt.le
  have hn : n*d+n*d ≤ 2^w := hB ▸ (p 2).isLt.le
  have hi : i.val = (arcs a).val := Nat.mod_eq_of_lt ((arcs a).isLt.trans_le ha)
  have hui : u.val = (bucketIndex site b).val := Nat.mod_eq_of_lt ((bucketIndex site b).isLt.trans_le hn)
  have hu : u < p 2 := by change u.val < _; rw [hui,hB]; exact (bucketIndex site b).isLt
  have hu' : u.val < 2*(n*d) := by have h := (bucketIndex site b).isLt; omega
  have legal : i < p 0 := by change i.val < _; rw [hi,hA]; exact (arcs a).isLt
  have ho : ownerAt p f i = u := by
    rw [owner_preserved p keys out widths dest reg sep pre hA done i (hA ▸ legal), filled.owners i legal,
      wordOwner_at P arcs site ha hn a,hb]
  have hhead : lengthAt R f i = f (countAt p u).val := by
    change f (p 3+ownerAt p f i).val = _; rw [ho]; rfl
  refine ⟨?_,?_,?_⟩
  · rw [hhead, count_preserved p keys out widths dest reg sep pre hB done u hu']
    exact (filled.rows u hu).1
  · rw [rank_start p keys out widths dest reg f i (ho ▸ hu'),ho,hui]
  · have keyfit := reg.keysFit
    change keys.val+A ≤ 2^w at keyfit
    change f (keys+i).val = _
    rw [Fin.val_add,hi,Nat.mod_eq_of_lt (by have := (arcs a).isLt; omega)]
    exact (done.inputs T reg (le_refl _)).2.1 _ (arcs a).isLt

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Readback of both classes from the one rank column indexed by the original ports. -/
structure Ranked (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (hc : 2 ≤ c)
    (dest : Word w) (m : Memory w) : Prop where
  motif : ∀ b (x : P.MotifFiber b), m (dest.val+(arcs x.val.val).val) =
    Fin.ofNat _ (P.sortedBundleNumbering vertices tags hc b x).val
  thick : ∀ b (x : P.ThickFiber b), m (dest.val+(arcs x.val.val).val) =
    Fin.ofNat _ (P.sortedThickNumbering hc b x).val

private theorem rank_after_scan (hc : 2 ≤ c) (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J)
    (fitM : N*(J*(d*(2^c*d))) ≤ 2^w) (fitT : 2^c*d ≤ 2^w)
    (reg : (T).Layout) (sep : RankLayout p keys out dest A (2*(n*d))) (pre : RowRegions p)
    (hA : (p 0).val = A) (hB : (p 2).val = n*d+n*d)
    (m : Memory w) (filled : PreimagesAt p (wordOwner P arcs site) m A)
    (motifs : ∀ x : P.Motif, m (keys.val+(arcs x.val).val) = (motifKey P vertices tags x).castLE fitM)
    (thick : ∀ x : P.ThickWire, m (keys.val+(arcs x.val).val) = (thickKey P x).castLE fitT) (scan : List (Report w) → Prop)
    (gather : ∀ (ha : A ≤ 2^w) (hn : n*d+n*d ≤ 2^w), Stored P arcs site p m →
      ∃ rs, scan rs ∧ (T).Completed m (after m (eventLog rs)) (2*(n*d)) ∧
        KeyRows P arcs site p keys out widths ha hn m (after m (eventLog rs)) ∧
        RAMBuckets.cost Report.probes rs = 4*A) :
    let cap := pieceCount d c
    let M := (template (visit cap) 0).instantiate w R
    ∃ gs rs, let f := after m (eventLog gs)
      scan gs ∧ (T).Completed m f (2*(n*d)) ∧
      SlotOwners.FilledRun M.program (1+(visit cap).length) (cap+4) (visit cap).length A dest
        (fun j ↦ result R f (Fin.ofNat _ j) cap) f rs ∧
      Ranked P arcs vertices tags hc dest (after f (eventLog rs)) ∧
      RAMBuckets.cost Report.probes gs + RAMBuckets.cost Report.probes rs = (cap+9)*A := by
  intro cap M
  have ha : A ≤ 2^w := hA ▸ (p 0).isLt.le
  have hn : n*d+n*d ≤ 2^w := hB ▸ (p 2).isLt.le
  have stored : Stored P arcs site p m := by
    intro b
    exact filled.rows _ (show (bucketIndex site b).val % (2^w) < (p 2).val by
      rw [Nat.mod_eq_of_lt ((bucketIndex site b).isLt.trans_le hn),hB]; exact (bucketIndex site b).isLt)
  obtain ⟨gs,run,done,read,cost⟩ := gather ha hn stored
  let f := after m (eventLog gs)
  have legal (i : Word w) (hi : i.val < A) : (ownerAt p f i).val < 2*(n*d) := by
    let j : Fin A := ⟨i.val,hi⟩
    have he : Fin.ofNat (2^w) j.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [owner_preserved p keys out widths dest reg sep pre hA done i hi,filled.owners i (show i.val < (p 0).val from hA ▸ hi),
      ← he,wordOwner,encodedPlacement_eq arcs (bucketIndex site) (bucketOf P) ha hn]
    have h := (bucketIndex site (bucketOf P (arcs.symm j))).isLt
    omega
  have rreg := rank_regions p keys out widths dest reg sep pre hA hB f legal
  have header := ranked_header P arcs site p keys out widths dest reg sep pre hA hB done filled
  obtain ⟨rs,ranks,hm,ht⟩ := graph_scan P arcs R f cap rreg vertices tags hc fitM fitT (fun b x ↦ by
    let i := Fin.ofNat (2^w) (arcs x.val.val).val
    let g : Fin 3 → Word w := ![0,keys,start R f i]
    let r := motifRow P arcs site ha hn b
    have hnum := header x.val.val (.inr b) ((bucketOf_motif P x.val).trans (congrArg Sum.inr x.prop))
    obtain ⟨hl,hs,hp⟩ := hnum
    have hlen := motifRow_length P hc b r
    have hkey := motif_read P arcs site ha hn vertices tags b m f g fitM motifs
      (fun j ↦ by change f ((start R f i).val+j.val) = _; rw [hs]; exact read _ j)
    refine ⟨r, ⟨?_, hlen.le, hp.trans (motifs x.val), ?_, hkey⟩⟩
    · exact hl.trans ((arcList_length P arcs site hc ha hn (.inr b)).trans hlen.symm)
    · rw [hs, hlen]
      apply rank_row_fits p keys out widths reg
      have h := (bucketIndex site (.inr b)).isLt; omega)
    (fun b x ↦ by
      let i := Fin.ofNat (2^w) (arcs x.val.val).val
      let g : Fin 3 → Word w := ![0,keys,start R f i]
      let r := thickRow P arcs site ha hn b
      have hnum := header x.val.val (.inl b) ((bucketOf_thick P x.val).trans (congrArg Sum.inl x.prop))
      obtain ⟨hl,hs,hp⟩ := hnum
      have hlen := thickRow_length P hc b r
      have hcap : r.ids.length ≤ cap := hlen.le.trans (Nat.div_le_div_right (by omega : 2^c*d ≤ 3*(2^c*d)))
      have hkey := thick_read P arcs site ha hn b m f g fitT thick
        (fun j ↦ by change f ((start R f i).val+j.val) = _; rw [hs]; exact read _ j)
      refine ⟨r, ⟨?_, hcap, hp.trans (thick x.val), ?_, hkey⟩⟩
      · exact hl.trans ((arcList_length P arcs site hc ha hn (.inl b)).trans hlen.symm)
      · rw [hs]
        apply (Nat.add_le_add_left hcap _).trans (rank_row_fits p keys out widths reg _ ?_)
        have h := (bucketIndex site (.inl b)).isLt; omega)
  exact ⟨gs,rs,run,done,ranks,⟨hm,ht⟩,by rw [cost,ranks.cost,← Nat.add_mul]; congr 1; omega⟩

/-- Build the rectangular key table from actual bounded ID rows, then execute
one rank call per original port in the resulting physical memory. -/
theorem ranked_table (hc : 2 ≤ c) (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J)
    (fitM : N*(J*(d*(2^c*d))) ≤ 2^w) (fitT : 2^c*d ≤ 2^w)
    (reg : (T).Layout) (sep : RankLayout p keys out dest A (2*(n*d))) (pre : RowRegions p)
    (hA : (p 0).val = A) (hB : (p 2).val = n*d+n*d)
    (m : Memory w) (filled : PreimagesAt p (wordOwner P arcs site) m A)
    (motifs : ∀ x : P.Motif, m (keys.val+(arcs x.val).val) = (motifKey P vertices tags x).castLE fitM)
    (thick : ∀ x : P.ThickWire, m (keys.val+(arcs x.val).val) = (thickKey P x).castLE fitT) :
    let cap := pieceCount d c
    let M := (template (visit cap) 0).instantiate w R
    ∃ gs rs, let f := after m (eventLog gs)
      (T).Runs m (2*(n*d)) gs ∧ (T).Completed m f (2*(n*d)) ∧
      SlotOwners.FilledRun M.program (1+(visit cap).length) (cap+4) (visit cap).length A dest
        (fun j ↦ result R f (Fin.ofNat _ j) cap) f rs ∧
      Ranked P arcs vertices tags hc dest (after f (eventLog rs)) ∧
      RAMBuckets.cost Report.probes gs + RAMBuckets.cost Report.probes rs = (cap+9)*A := by
  apply rank_after_scan P arcs site p keys out widths dest hc vertices tags fitM fitT reg sep pre hA hB m filled motifs thick
  intro ha hn stored
  exact gather_table P arcs site p keys out widths hc ha hn reg m stored

/-- Execute both whole-table scans using one fixed bank each. -/
theorem fixed_ranked_table (hc : 2 ≤ c) (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J)
    (fitM : N*(J*(d*(2^c*d))) ≤ 2^w) (fitT : 2^c*d ≤ 2^w)
    (reg : (T).Layout) (sep : RankLayout p keys out dest A (2*(n*d))) (pre : RowRegions p)
    (hA : (p 0).val = A) (hB : (p 2).val = n*d+n*d)
    (m : Memory w) (filled : PreimagesAt p (wordOwner P arcs site) m A)
    (motifs : ∀ x : P.Motif, m (keys.val+(arcs x.val).val) = (motifKey P vertices tags x).castLE fitM)
    (thick : ∀ x : P.ThickWire, m (keys.val+(arcs x.val).val) = (thickKey P x).castLE fitT) :
    let cap := pieceCount d c
    let M := (template (visit cap) 0).instantiate w R
    ∃ gs rs, let f := after m (eventLog gs)
      Fixed.FullRun (Fixed.parameters T) m (Fixed.slot T reg) gs ∧ (T).Completed m f (2*(n*d)) ∧
      SlotOwners.FilledRun M.program (1+(visit cap).length) (cap+4) (visit cap).length A dest
        (fun j ↦ result R f (Fin.ofNat _ j) cap) f rs ∧
      Ranked P arcs vertices tags hc dest (after f (eventLog rs)) ∧
      RAMBuckets.cost Report.probes gs + RAMBuckets.cost Report.probes rs = (cap+9)*A := by
  apply rank_after_scan P arcs site p keys out widths dest hc vertices tags fitM fitT reg sep pre hA hB m filled motifs thick
  intro ha hn stored
  exact fixed_gather_table P arcs site p keys out widths hc (hA ▸ (p 0).isLt) hn reg m stored

end CompressorRecords.BundleGather

end VPVNP
end Computability
end OAI

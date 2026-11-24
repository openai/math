import OAI.Computability.VPVNP.CompressorBundleRankedTable
import OAI.Computability.VPVNP.CompressorRecordsBundleWidthScatter

/-!
# Sorted width rows from the bounded lists of old ports

Run the global key gather, the increasing-port rank scan, and the width scatter
on their successive post-memories. The resulting thick rows give the
concatenation order used to assemble AB blocks. Motif rows give the old CD
widths in piece-number order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleWidthScatter

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.PackingData
open BundleGather BundleLists BundleRank

variable {V H Tag L : Type} {n d c A w N J : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

/-- Use the original owner/width columns and the completed rank destination.
The sorted width rectangle has the same stride as the bounded lists. -/
def scatterPublic (p : Fin 6 → Word w) (dest widths sorted : Word w) : Fin 5 → Word w :=
  ![p 1,dest,widths,p 4,sorted]

variable (P : PackingData V H Tag L d c) (arcs : Arc V H Tag L d c ≃ Fin A)
variable (site : Site V Tag L ≃ Fin n) (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (hc : 2 ≤ c)
variable (p : Fin 6 → Word w) (keys out widths dest sorted : Word w)

local notation "T" => table A n d c p keys out widths
local notation "R" => rankPublic p keys out dest
local notation "S" => scatterPublic p dest widths sorted
local notation "CD" => P.sortedBundleNumbering vertices tags hc
local notation "DD" => P.sortedThickNumbering hc

omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag]
  [Fintype L] [DecidableEq V] [DecidableEq Tag] [DecidableEq L] in
private theorem source_val {q : Fin 5 → Word w} (layout : Layout q A n d c)
    (t : Fin 3) (a : Arc V H Tag L d c) :
    (source q t (arcWord arcs a)).val = (q (t.castAdd 2)).val + (arcs a).val := by
  have h := layout.sourceFits t
  have hi := (arcs a).isLt
  rw [source, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]

/-- Three successive native passes produce the exact sorted width rows directly
from the preimage table, the classified keys, and the old width column. -/
theorem sorted_widths (fitM : N*(J*(d*(2^c*d))) ≤ 2^w) (fitT : 2^c*d ≤ 2^w)
    (reg : (T).Layout) (sep : RankLayout p keys out dest A (2*(n*d))) (pre : RowRegions p)
    (space : Layout S A n d c) (widthsApart : separated widths.val A dest.val A)
    (hA : (p 0).val = A) (hB : (p 2).val = n*d+n*d) (m : Memory w)
    (filled : PreimagesAt p (wordOwner P arcs site) m A)
    (motifs : ∀ x : P.Motif, m (keys.val+(arcs x.1).val) = (motifKey P vertices tags x).castLE fitM)
    (thick : ∀ x : P.ThickWire, m (keys.val+(arcs x.1).val) = (thickKey P x).castLE fitT)
    (old : Arc V H Tag L d c → ℕ) (oldWidths : ∀ a, (m (widths.val+(arcs a).val)).val = old a) :
    let cap := pieceCount d c
    let M := (template (PortRankRAM.visit cap) 0).instantiate w R
    let W := (template visit 0).instantiate w S
    ∃ gs rs ws, let f := after m (eventLog gs)
                let g := after f (eventLog rs)
                let final := after g (eventLog ws)
      (T).Runs m (2*(n*d)) gs ∧ (T).Completed m f (2*(n*d)) ∧
      SlotOwners.FilledRun M.program (1+(PortRankRAM.visit cap).length) (cap+4)
        (PortRankRAM.visit cap).length A dest (fun j ↦ PortRankRAM.result R f (word j) cap) f rs ∧
      Ranked P arcs vertices tags hc dest g ∧
      runSegment W.program 19 (some 0) g (List.replicate A []) = some ws ∧
      endState (some 0) ws = some (word A) ∧ Filled S g final A ∧
      ws.length = A ∧ (∀ r ∈ ws, r.events.length = 18 ∧ r.probes = 4) ∧
      (∀ b i, (final ((rowBase S site (.inl b)).val + i.val)).val = old ((DD b).symm i).1.1) ∧
      (∀ b i, (final ((rowBase S site (.inr b)).val + i.val)).val = old ((CD b).symm i).1.1) ∧
      RAMBuckets.cost Report.probes gs + RAMBuckets.cost Report.probes rs +
        RAMBuckets.cost Report.probes ws = (cap+14)*A := by
  intro cap M W
  obtain ⟨gs,rs,gr,gd,rr,rd,cost⟩ := ranked_table P arcs site p keys out widths dest hc vertices tags fitM fitT
    reg sep pre hA hB m filled motifs thick
  let f := after m (eventLog gs)
  let g := after f (eventLog rs)
  have ha : A ≤ 2^w := hA ▸ (p 0).isLt.le
  have hb : n*d+n*d ≤ 2^w := hB ▸ (p 2).isLt.le
  have hinput : RankedInput P CD DD arcs site S g old := by
    constructor
    · intro a
      have hi := (arcs a).isLt
      have hid : (arcWord (w := w) arcs a).val = (arcs a).val := Nat.mod_eq_of_lt (hi.trans_le ha)
      have hslot : (source S 0 (arcWord arcs a)).val = (p 1).val+(arcs a).val := source_val arcs space 0 a
      dsimp only [g, f]
      rw [hslot, rr.frame _ (sep.owners.outside hi), gd.outside T reg (le_refl _) _ (sep.keepOwners.outside hi)]
      have hread := filled.owners (arcWord arcs a) (show (arcWord arcs a).val < (p 0).val by rw [hid,hA]; exact hi)
      rw [wordOwner_at P arcs site ha hb a] at hread
      change m (source S 0 (arcWord arcs a)).val = _ at hread
      rwa [hslot] at hread
    · intro a
      have hslot : (source S 1 (arcWord arcs a)).val = dest.val+(arcs a).val := source_val arcs space 1 a
      rw [hslot]
      by_cases ht : P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))
      · let x : P.ThickFiber a.1 := ⟨⟨a,ht⟩,rfl⟩
        rw [show rankOf P CD DD a = (DD _ x).val from rank_thick P CD DD x]
        exact rd.thick _ x
      · let m' : P.Motif := ⟨a,ht⟩
        let x : P.MotifFiber (P.bundle m') := ⟨m',rfl⟩
        rw [show rankOf P CD DD a = (CD _ x).val from rank_motif P CD DD x]
        exact rd.motif _ x
    · intro a
      have hi := (arcs a).isLt
      have hslot : (source S 2 (arcWord arcs a)).val = widths.val+(arcs a).val := source_val arcs space 2 a
      dsimp only [g, f]
      rw [hslot, rr.frame _ (widthsApart.outside hi)]
      exact (congrArg Fin.val ((gd.inputs T reg (le_refl _)).2.2 _ hi)).trans (oldWidths a)
  obtain ⟨ws,wr,wc,wd,wl,ww,costW,th,cd⟩ := graph_run P CD DD arcs site S g old space hinput
  refine ⟨gs,rs,ws,gr,gd,rr,rd,wr,wc,wd,wl,ww,th,cd,?_⟩
  rw [cost,costW,← Nat.add_mul]

end CompressorRecords.BundleWidthScatter

end VPVNP
end Computability
end OAI

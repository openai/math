import OAI.Computability.VPVNP.PairShrinkCallHeader
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Retaining the old tables used by shrink map calls

An old level supplies three incidence columns, four preliminary placement
columns and the classifier's lists and ranks. Agreement on these allocated
regions transports all typed readbacks into the online scheduler's memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallHeader

open Compression Compression.PackingData CompressorRecords BurstRAM BundleLists
open ShrinkRankSpace
open private rowAt_val countAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan

variable {a g w : ℕ} {X : State a (packingLaneBits a g)}
variable {mem out : Memory w} {origin : ℕ} {T : IncidenceDirectory w}
variable {D : ℕ → Prop}

local notation "Z" => ShrinkInput.plan X origin
local notation "q" => Shape.collectBank (ShrinkInput.plan X origin) w
local notation "pre" => ShrinkInput.placementBank X T origin
local notation "arcs" => BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "place" => wordOwner (w := w) X.packingData arcs sites
local notation "A" => IncidenceDirectory.slotCount X
local notation "S" => Fintype.card X.Base * 2 ^ packingLaneBits a g

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

private theorem row_capacity (geo : Geometry (w := w) X origin) (u : Word w) (hu : u < q 2) :
    (preimagePrefix place u A).length ≤ (q 4).val := by
  let j : Fin ((Z).B + (Z).B) := ⟨u.val, geo.nrows ▸ hu⟩
  obtain ⟨b, eqn⟩ := (bucketIndex sites (d := 2 ^ a)).surjective j
  have eu : Fin.ofNat (2 ^ w) (bucketIndex sites b).val = u := by
    rw [eqn]
    exact Fin.ext (Nat.mod_eq_of_lt u.isLt)
  rw [← eu]
  change (arcList X.packingData arcs sites b).length ≤ _
  rw [arcList_length X.packingData arcs sites (State.two_le_packingColors a)
    geo.arcFit geo.bucketFit]
  cases b with
  | inl b => exact (Nat.div_le_div_right (by omega :
      2 ^ (Shrink.colors a) * 2 ^ a ≤ 3 * (2 ^ (Shrink.colors a) * 2 ^ a))).trans geo.cap
  | inr b => exact geo.cap

private theorem column_agree {base i : Word w} {length : ℕ}
    (fit : base.val + length ≤ 2 ^ w) (index : i.val < length)
    (agree : SourceTransport.Agree D mem out)
    (cells : ∀ z, base.val ≤ z → z < base.val + length → D z) :
    out (base + i).val = mem (base + i).val := by
  apply (agree _ _).symm
  rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  exact cells _ (Nat.le_add_right ..) (Nat.add_lt_add_left index _)

/-- Carry the old level's typed port, rank, list and placement tables to any
memory which agrees on their physical regions. -/
theorem OldTables.transfer (h : OldTables X mem T origin)
    (room : (Z).stop < 2 ^ w)
    (oldFit : ∀ c : Fin 3, (T.column (c.natAdd 3)).val + A ≤ 2 ^ w)
    (agree : SourceTransport.Agree D mem out)
    (columns : ∀ (c : Fin 3) z, (T.column (c.natAdd 3)).val ≤ z →
      z < (T.column (c.natAdd 3)).val + A → D z)
    (classify : ∀ z, (Z).owner ≤ z → z < (Z).stop → D z)
    (preliminary : ∀ z, ShrinkInput.placementBase X origin ≤ z →
      z < ShrinkInput.rankBase X origin → D z) :
    OldTables X out T origin := by
  have geo := geometry X T origin room
  have v := (Z).values T pre Fintype.card_pos room
  have own : (q 1).val = (Z).owner := v.owner
  have ownersCounts := geo.regions.ownersBeforeCounts
  have countsRows := geo.regions.countsBeforeRows
  have rowTop : (q 5).val + (q 2).val * (q 4).val = (Z).gathered := by
    rw [v.ids, v.buckets, v.stride]
    rfl
  have gatheredRank : (Z).gathered ≤ (Z).ranks := Nat.le_add_right ..
  have rankStop : (Z).ranks + A = (Z).stop := rfl
  have ownerCells (i : Word w) (hi : i.val < A) :
      out (q 1 + i).val = mem (q 1 + i).val := by
    have size : (q 0).val = A := v.count
    refine column_agree (length := A) (by omega) hi agree ?_
    intro z lo lt
    exact classify z (own ▸ lo) (by omega)
  have column (c : Fin 3) (i : Word w) (hi : i.val < A) :
      out (T.column (c.natAdd 3) + i).val = mem (T.column (c.natAdd 3) + i).val :=
    column_agree (oldFit c) hi agree (columns c)
  constructor
  · constructor
    · intro i hi
      exact (ownerCells i ((show i.val < (q 0).val from hi).trans_eq v.count)).trans
        (h.preimages.owners i hi)
    · intro u hu
      obtain ⟨count, entries⟩ := h.preimages.rows u hu
      constructor
      · rw [(agree _ _).symm]
        · exact count
        · rw [countAt_val geo.regions hu]
          have index : u.val < (q 2).val := hu
          apply classify <;> omega
      · intro i
        rw [(agree _ _).symm]
        · exact entries i
        · rw [rowAt_val geo.regions hu]
          have hi := i.isLt.trans_le (row_capacity geo u hu)
          have next := Nat.mul_le_mul_right (q 4).val (show u.val + 1 ≤ (q 2).val from hu)
          rw [Nat.succ_mul] at next
          apply classify <;> omega
  · have index (e : BundleKeys.OldArc X.Base a g) :
        (BundleWidthScatter.arcWord (w := w) arcs e).val < A :=
      (Nat.mod_le ..).trans_lt (arcs e).isLt
    constructor
    · intro e
      exact (ownerCells _ (index e)).trans (h.ranked.owners e)
    · intro e
      apply Eq.trans _ (h.ranked.ranks e)
      refine column_agree (base := Fin.ofNat (2 ^ w) (Z).ranks) (length := A)
        (by rw [v.ranks, rankStop]; exact room.le) (index e) agree ?_
      intro z lo hi
      rw [v.ranks] at lo hi
      exact classify z (by omega) (rankStop ▸ hi)
    · intro e
      exact (congrArg Fin.val (column 2 _ (index e))).trans (h.ranked.widths e)
  · constructor
    · intro e
      exact (column 0 _ (IncidenceDirectory.actualPort_lt X e)).trans (h.incidence.actualOut e)
    · intro e
      exact (column 1 _ (IncidenceDirectory.actualPort_lt X e)).trans (h.incidence.actualIn e)
    · intro e
      exact (column 2 _ (IncidenceDirectory.actualPort_lt X e)).trans (h.incidence.width e)
  · constructor
    intro x P i
    have hi : i.val < S := by
      change (Shrink.oldNumber X.baseIndex x) % (2 ^ w) < _
      rw [← Shrink.oldIndex_val]
      exact (Nat.mod_le ..).trans_lt (Fin.isLt _)
    have rankRoom : ShrinkInput.rankBase X origin < 2 ^ w :=
      (ShrinkInput.range_bounds X origin).2.2.1.trans_lt room
    have keep (c : Fin 4) : out (ShrinkRAM.outAddr pre c i) = mem (ShrinkRAM.outAddr pre c i) := by
      have start : (pre (c.natAdd 10)).val = ShrinkInput.placementBase X origin + c.val * S :=
        ShrinkPlacement.starts X T _ _ _ false rankRoom c
      have stop : (pre (c.natAdd 10)).val + S ≤ ShrinkInput.rankBase X origin := by
        rw [start]
        change _ ≤ ShrinkInput.placementBase X origin + 4 * S
        have hc := Nat.mul_le_mul_right S c.isLt
        rw [Nat.succ_mul] at hc
        omega
      apply column_agree (length := S) (stop.trans rankRoom.le) hi agree
      intro z lo lt
      apply preliminary z _ (lt.trans_le stop)
      rw [start] at lo
      omega
    rw [keep 0, keep 1, keep 2, keep 3]
    exact h.thickness.atSite x

end PairSimulation.ShrinkCallHeader

end VPVNP
end Computability
end OAI

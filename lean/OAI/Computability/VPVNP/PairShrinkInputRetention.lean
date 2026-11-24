import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables
import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch
import OAI.Computability.VPVNP.CompressorShrinkResidentRun
import OAI.Computability.VPVNP.PairShrinkCallHeader

/-!
# Reading original arc lists and ranks during a shrinking simulation

The append pass lists old outgoing identifiers in scan order. The gather pass
writes its keys above these lists, and the rank pass writes above the keys.
The absolute-identifier scatter reuses the gathered-key rectangle. The list
rows, counters and owners lie below that rectangle, and the ranks lie above
it. Consequently the simulation can combine the original scan-order lists
with the ranks in the selected ordering in the same memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput.Run

open BurstRAM Compression Compression.PackingData BundleLists BundleKeys
open ShrinkRankSpace BundleGather
open private rowAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w}
variable {start : ℕ} {m : Memory w} (r : Run X T start m)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "Z" => plan X start
local notation "A" => Shape.A (plan X start)
local notation "B" => Shape.B (plan X start)
local notation "P" => X.packingData
local notation "arcs" => oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "q" => Shape.collectBank (plan X start) w
local notation "rankHead" => Fin.ofNat (2 ^ w) (Shape.ranks (plan X start))
local notation "s" => ShrinkWidthArena.scatterBank T q rankHead (widthBase X start)
local notation "ms" => after r.greedy.post (eventLog r.sites)
local notation "ml" => after (after (after ms (eventLog r.clear)) (eventLog r.classify))
  (eventLog r.append)
local notation "mg" => after ml (eventLog r.gather)

/-- Below the gathered-key rectangle the width, rank, and gather scans all
preserve the memory left by the original list builder. -/
theorem post_eq_append (room : stop X start < 2 ^ w) {z : ℕ} (hz : z < (Z).gathered) :
    r.post z = ml z := by
  have ranges := range_bounds X start
  have fit := ranges.2.2.2.trans_lt room
  have v := (Z).values T (placementBank X T start) Fintype.card_pos fit
  have layout := ((Z).regions T (placementBank X T start) Fintype.card_pos
    ((r.greedy.old 5).trans (ranges.1.trans ranges.2.1)) fit).2.1
  have hn : B + B ≤ 2 ^ w := by rw [← two_mul, ← v.buckets]; exact (q 2).isLt.le
  have stored : BundleGather.Stored P arcs sites q ml := by
    intro b
    apply r.ranking.ranked.lists.rows
    change (bucketIndex sites b).val % (2 ^ w) < (q 2).val
    rw [Nat.mod_eq_of_lt ((bucketIndex sites b).isLt.trans_le hn), v.buckets, two_mul]
    exact (bucketIndex sites b).isLt
  have ha : A < 2 ^ w := (Z).scalarFits Fintype.card_pos fit |>.1
  let K := (Z).gatheredTable w T
  obtain ⟨rs, run, done, _, _⟩ := fixed_gather_table P arcs sites q
    (Fin.ofNat _ (Z).key) (Fin.ofNat _ (Z).gathered) T.width
    (State.two_le_packingColors a) ha hn layout ml stored
  have count : Fixed.entryCount K = A := by
    change B * (2 ^ (Shrink.colors a) * 2 ^ a / 4 + (Z).Q) = A
    rw [Nat.mul_add]; exact bundle_rows_total ..
  have execute := run.executed
  change runSegment _ _ _ _ (List.replicate (Fixed.entryCount K) []) = some rs at execute
  rw [count] at execute
  have eqn : rs = r.gather := Option.some.inj (execute.symm.trans r.ranking.ranked.gather)
  subst rs
  have gather : mg z = ml z := done.outside K layout le_rfl z (.inl (v.gathered ▸ hz))
  have hr := hz.trans_le (Nat.le_add_right (Z).gathered (Z).rectangleSize)
  have zrank : z < (rankHead).val := by rw [v.ranks]; exact hr
  have ranks : r.rankPost z = mg z := r.ranking.ranked.rank.frame z (.inl zrank)
  exact (r.afterRank z (hr.trans_le (Nat.le_add_right (Z).ranks A))).trans (ranks.trans gather)

/-- The complete old-port lists in any later snapshot that preserves the
part of the shrinking directory preceding the gathered keys. -/
theorem original_preimages {out : Memory w} (room : stop X start < 2 ^ w)
    (low : ∀ z < (Z).gathered, out z = r.post z) :
    PreimagesAt q (wordOwner P arcs sites) out A := by
  let place := wordOwner (w := w) P arcs sites
  have before := range_bounds X start
  have fit := before.2.2.2.trans_lt room
  have v := (Z).values T (placementBank X T start) Fintype.card_pos fit
  have reg := ((Z).regions T (placementBank X T start) Fintype.card_pos
    ((r.greedy.old 5).trans (before.1.trans before.2.1)) fit).1
  have read (z : ℕ) (hz : z < (Z).gathered) : out z = ml z :=
    (low z hz).trans (r.post_eq_append room hz)
  have top : (q 5).val + (q 2).val * (q 4).val = (Z).gathered := by
    rw [v.ids, v.buckets, v.stride]; rfl
  have scalars := (Z).scalarFits Fintype.card_pos fit
  have bucketCount : (q 2).val = B + B := v.buckets.trans (two_mul _)
  have capacity (u : Word w) (hu : u < q 2) : (preimagePrefix place u A).length ≤ (q 4).val := by
    let j : Fin (B + B) := ⟨u.val, bucketCount ▸ hu⟩
    let b := (bucketIndex sites (d := 2 ^ a)).symm j
    have idx : (bucketIndex sites b).val = u.val :=
      congrArg Fin.val ((bucketIndex sites).apply_symm_apply j)
    have idWord : Fin.ofNat (2 ^ w) (bucketIndex sites b).val = u := by
      rw [idx]; exact Fin.ext (Nat.mod_eq_of_lt u.isLt)
    rw [← idWord]
    change (arcList P arcs sites b).length ≤ _
    rw [arcList_length P arcs sites (State.two_le_packingColors a)
      scalars.1.le (by rw [← two_mul]; exact scalars.2.1.le), v.stride]
    cases b with
    | inl b => exact Nat.div_le_div_right (by omega : 2 ^ (Shrink.colors a) * 2 ^ a ≤
          3 * (2 ^ (Shrink.colors a) * 2 ^ a))
    | inr b => exact le_rfl
  have filled : PreimagesAt q place ml A := r.ranking.ranked.lists
  constructor
  · intro i hi
    have hi' : i.val < (q 0).val := hi
    have bound := ((Nat.add_lt_add_left hi' (q 1).val).trans_le reg.ownersBeforeCounts).trans_le
      ((Nat.le_add_right ..).trans reg.countsBeforeRows)
    unfold ownerAt
    rw [read _ (by rw [Fin.val_add]; exact (Nat.mod_le ..).trans_lt (by omega))]
    exact filled.owners i hi
  · intro u hu
    have cap := capacity u hu
    have hcount := (Nat.add_lt_add_left (show u.val < (q 2).val from hu) (q 3).val).trans_le
      reg.countsBeforeRows
    have hlen := Nat.mul_le_mul_right (q 4).val (show u.val + 1 ≤ (q 2).val from hu)
    rw [Nat.succ_mul] at hlen
    obtain ⟨length, data⟩ := filled.rows u hu
    constructor
    · rw [read _ (by rw [countAt, Fin.val_add]; exact (Nat.mod_le ..).trans_lt (by omega))]
      exact length
    · intro i
      have hi := i.isLt.trans_le cap
      rw [read _ (by rw [rowAt_val reg hu]; omega)]
      exact data i

include r in
private theorem packing_width_fits (e : OldArc X.Base a g) : X.packingWidth e < 2 ^ w := by
  by_cases h : (P).thick (sourcePosition e) ∧ (P).thick (sourcePosition ((P).actual e))
  · let x : (P).ThickFiber e.1 := ⟨⟨e, h⟩, rfl⟩
    have width := r.stored.thickWidths e.1 (X.shrinkOrder e.1 x)
    rw [Equiv.symm_apply_apply] at width
    change _ = X.packingWidth e at width
    rw [← width]
    exact Fin.isLt _
  · let y : (P).Motif := ⟨e, h⟩
    let x : (P).MotifFiber ((P).bundle y) := ⟨y, rfl⟩
    have width := r.stored.cdWidths ((P).bundle y) (X.shrinkNumber ((P).bundle y) x)
    rw [Equiv.symm_apply_apply] at width
    change _ = X.packingWidth e at width
    rw [← width]
    exact Fin.isLt _

/-- Original ranks, owners and exact widths. The later snapshot need only
agree on the lower directory and the rank column. The gathered keys may
have already been reused for absolute motif IDs. -/
theorem original_ranked {out : Memory w} (room : stop X start < 2 ^ w)
    (low : ∀ z < (Z).gathered, out z = r.post z)
    (rank : ∀ z, (Z).ranks ≤ z → z < widthBase X start → out z = r.post z) :
    BundleWidthScatter.RankedInput P X.shrinkNumber X.shrinkOrder arcs sites s out
      X.packingWidth := by
  have before := range_bounds X start
  have fit := before.2.2.2.trans_lt room
  have v := (Z).values T (placementBank X T start) Fintype.card_pos fit
  have ai := ShrinkBundlePlan.absolute_inputs r fit
  have old : T.width.val + A ≤ start := r.greedy.old 5
  have owner : (q 1).val = (Z).owner := v.owner
  have og : (Z).owner + A ≤ (Z).gathered := by
    change (Z).owner + A ≤ (Z).owner + 2 * A + 2 * B + (Z).rectangleSize
    omega
  have wg : T.width.val + A ≤ (Z).gathered := old.trans ((before.1.trans before.2.1).trans
    ((Nat.le_add_right (Z).owner A).trans og))
  constructor
  · intro e
    have he := (arcs e).isLt
    change out (q 1 + Fin.ofNat _ (arcs e).val).val = _
    rw [low _ (by
      rw [Fin.val_add, Fin.val_ofNat, owner]
      exact (Nat.mod_le ..).trans_lt
        ((Nat.add_lt_add_left ((Nat.mod_le ..).trans_lt he) _).trans_le og))]
    exact ai.owners e
  · intro e
    have he : (arcs e).val < A := (arcs e).isLt
    have top : (Z).ranks + A < 2 ^ w := fit
    have addr : (rankHead + Fin.ofNat _ (arcs e).val).val = (Z).ranks + (arcs e).val := by
      rw [Fin.val_add, v.ranks, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    change out (rankHead + Fin.ofNat _ (arcs e).val).val = _
    rw [rank _ (addr ▸ Nat.le_add_right ..)
      (addr ▸ Nat.add_lt_add_left he (Z).ranks)]
    exact ai.ranks e
  · intro e
    have he : (arcs e).val < A := (arcs e).isLt
    have hz := (Nat.add_lt_add_left he T.width.val).trans_le wg
    have hbelow : (Z).gathered ≤ widthBase X start :=
      (Nat.le_add_right (Z).gathered _).trans (Nat.le_add_right (Z).ranks A)
    change (out (T.width + Fin.ofNat _ (arcs e).val).val).val = _
    rw [Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (hz.trans_le
      (hbelow.trans fit.le)), low _ hz, r.afterRank _ (hz.trans_le hbelow)]
    exact (congrArg Fin.val (r.ranking.widths e)).trans (Nat.mod_eq_of_lt (r.packing_width_fits e))

/-- Read both tables after the native absolute scatter and subsequent stages
which preserve the shrinking input area. -/
theorem original_after_absolute {rs : List (Report w)}
    (last : ShrinkBundlePlan.AbsoluteRun r rs) {out : Memory w} (room : stop X start < 2 ^ w)
    (keep : ∀ z < widthBase X start, out z = after r.post (eventLog rs) z) :
    PreimagesAt q (wordOwner P arcs sites) out A ∧
      BundleWidthScatter.RankedInput P X.shrinkNumber X.shrinkOrder arcs sites s out
        X.packingWidth := by
  have bound : (Z).gathered ≤ widthBase X start :=
    (Nat.le_add_right (Z).gathered _).trans (Nat.le_add_right (Z).ranks A)
  have low (z) (hz : z < (Z).gathered) :=
    (keep z (hz.trans_le bound)).trans (last.frame z (.inl hz))
  exact ⟨r.original_preimages room low, r.original_ranked room low
    (fun z hr hw ↦ (keep z hw).trans (last.frame z (.inr hr)))⟩

end CompressorRecords.ShrinkInput.Run

namespace CompressorRecords.ShrinkOutput

open Compression BurstRAM ShrinkBlockInputs BundleLists BundleKeys ShrinkResidentRun
open Compression.ShrinkMotif

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {i : Fin S.steps}
variable {g w : ℕ} {δ : ℝ} {X : State (a i) (packingLaneBits (a i) g)}
variable {ready : Ready (2 ^ a i) (Shrink.colors (a i)) (2 ^ b i) δ}
variable {T : IncidenceDirectory w} {start cap : ℕ} {stride selectors : Word w}
variable {sel : SelectedScore.Selection B X} {m : Memory w}
variable {p : ShrinkBranch.Prefix X T start cap m}
variable (v : ShrinkBranch.Selected B X T start stride selectors cap m p sel)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "absHead" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Read all original inputs of a resident map in the final snapshot produced
by the hidden and map directories, the AB intersections, and the surviving
and ordered-slot scans. Later stages may reuse the gathered-key rectangle. -/
theorem CompleteTables.old_call_tables
    {resident first width slotStart : ℕ} {role : Word w} {side : Bool}
    {h u : ShrinkResidentRun.Passes w}
    (hiddenRun : Built X resident absHead role side false v.beforeOutput h)
    (mapRun : Built X resident absHead role side true (h.final v.beforeOutput) u)
    {I : ShrinkABSliceRecipe.Inputs} {pub : Fin 5 → Word w} {state : Word w} {ref : Memory w}
    {r : TablesRun w} (tables : CompleteTables B i X ready sel term stride absHead start
      I pub state ref first width slotStart cap (u.final (h.final v.beforeOutput)) r)
    (room : ShrinkInput.termEnd X start stride.val < 2 ^ w)
    (residentFresh : ShrinkInput.stop X start ≤ resident)
    (abFresh : ShrinkInput.stop X start ≤ first) (order : first ≤ width) :
    PairSimulation.ShrinkCallHeader.OldTables X r.final T start := by
  have frame (x : ℕ) (hx : x < ShrinkInput.stop X start) :
      r.final x = after p.input.post (eventLog p.absolute) x := by
    have beforeHidden := (hx.trans_le residentFresh).trans_le
      ((ShrinkResidentLayout.layout X resident).ranges false).1
    have beforeMaps := (hx.trans_le residentFresh).trans_le
      ((ShrinkResidentLayout.layout X resident).ranges true).1
    have beforeAB := hx.trans_le abFresh
    have beforeSlots := (beforeAB.trans_le order).trans_le
      (retained_room X term stride.val (SelectedArena.roleBase X term stride) width)
    exact (tables.remainder.construction.frame x (.inl beforeSlots)).trans
      ((tables.abFrame x (.inl beforeAB)).trans ((mapRun.frame x (.inl beforeMaps)).trans
        ((hiddenRun.frame x (.inl beforeHidden)).trans (v.lowerFrame x hx))))
  have stopRoom : ShrinkInput.stop X start < 2 ^ w := by
    unfold ShrinkInput.termEnd at room
    omega
  obtain ⟨rows, ranked⟩ := p.input.original_after_absolute p.absoluteRun stopRoom
    (fun x hx ↦ frame x (hx.trans_le (ShrinkInput.range_bounds X start).2.2.2))
  have geometry := p.input.keepAbsoluteThenTerms p.absoluteRun.frame stride.val room frame
  exact ⟨rows, ranked, geometry.incidence.actual, geometry.placement⟩

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI

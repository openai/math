import OAI.Computability.VPVNP.PairShrinkABFrameAddress
import OAI.Computability.VPVNP.CompressorShrinkBundlePlan

/-!
# Direct pointers to the two unsplit CD operands

The motif's rank is relative to its bundle. Its classified row contains old
arc IDs in append order. A fixed-size rank comparison retrieves the matching
original ID. The thickness column at its source chooses which of the two
private child halves belongs to C and which belongs to D.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCD

open Compression Compression.PackingData CompressorRecords CompressorRecords.PhaseRecipe
open BurstRAM BurstRAM.PrivateRAM BundleLists
open scoped Fin.CommRing

/-- Runtime operands for finding the CD demand's old arc and choosing the correct private half
at C or D. -/
structure Header where
  /-- The shared bundle lists, ranks, motif ordinal, and old half-wire geometry used by the CD
  lookup. -/
  fields : ShrinkAB.Physical.Header
  /-- Number of classified owner rows. Half this count is the displacement to the CD half of
  the row rectangle. -/
  owners : Expr
  /-- Head of the array of old-site thickness flags used to orient the two CD endpoints. -/
  thickness : Expr

/-- CD rows occupy the second half of the classified row rectangle. -/
def Header.row (H : Header) (pieces : ℕ) : Expr :=
  let b := (H.owners.div (.lit 2)).add (H.fields.bundle pieces)
  H.fields.lists.add (b.mul H.fields.listStride)

/-- Read an old arc ID at a fixed column of the selected bundle's CD row. -/
def Header.candidate (H : Header) (pieces index : ℕ) : Expr :=
  .load ((H.row pieces).add (.lit index))

/-- A nonzero modular difference divided by itself is one. A zero
difference divided by itself is zero, including at the largest word. -/
def equal (x y : Expr) : Expr :=
  let z := x.sub y
  (Expr.lit 1).sub (z.div z)

/-- Keep the candidate's arc ID exactly when its stored rank equals the motif's piece number,
and return zero otherwise. -/
def Header.select (H : Header) (pieces index : ℕ) : Expr :=
  let id := H.candidate pieces index
  let rank := Expr.load (H.fields.rankBase.add id)
  (equal rank (H.fields.piece pieces)).mul id

/-- Sum the rank-filtered CD row entries to recover the old arc ID at the selected piece. -/
def Header.arc (H : Header) (pieces : ℕ) : Expr :=
  PortRefresh.ArgumentAddress.sum ((List.finRange pieces).map fun i ↦ H.select pieces i.val)

/-- Read the thickness flag of the old source site, whose ordinal is the selected CD arc ID
divided by the old degree. -/
def Header.flag (H : Header) (degree pieces : ℕ) : Expr :=
  .load (H.thickness.add ((H.arc pieces).div (.lit degree)))

/-- C follows the incoming half when its old source is thick. D follows
the complementary half. Each source address uses the numbered child arena. -/
def Header.field (H : Header) (degree pieces : ℕ) (atD : Bool) : Expr :=
  let arc := H.arc pieces
  let flag := H.flag degree pieces
  let incoming := if atD then (Expr.lit 1).sub flag else flag
  let out := H.fields.oldHalf.field degree arc false
  let inc := H.fields.oldHalf.field degree arc true
  (incoming.mul inc).add (((Expr.lit 1).sub incoming).mul out)

variable {a g w : ℕ} (X : State a (packingLaneBits a g))
local notation "P" => X.packingData
local notation "d" => 2 ^ a
local notation "c" => Shrink.colors a
local notation "arcs" => BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "arcCount" => Fintype.card X.Base * 2 ^ (packingLaneBits a g) * d
local notation "bundles" => (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * d
local notation "pieces" => pieceCount d c

/-- Classical equality of base vertices used in the classified CD fiber lookup. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Each row index decodes to a different motif, and every motif in the
bundle occurs at one index. -/
noncomputable def members (arcFit : arcCount ≤ 2 ^ w) (bucketFit : bundles + bundles ≤ 2 ^ w)
    (b : Port X.Base (BitWord (Shrink.J a)) (BitWord g) d) : Fin pieces ≃ (P).MotifFiber b :=
  let size := arcList_length (P) arcs sites (State.two_le_packingColors a) arcFit bucketFit (.inr b)
  ((finCongr size.symm).trans (ordinalEquiv (P) arcs sites arcFit bucketFit (.inr b))).trans
    (motifEquiv (P) b)

variable (H : Header) (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
variable {q : Fin 6 → Word w} {s : Fin 5 → Word w} {first dest : ℕ}
variable (m : X.packingData.Motif) (stored : H.fields.Stored X pub state mem q s first dest m)
variable (arcFit : Fintype.card X.Base * 2 ^ (packingLaneBits a g) * 2 ^ a ≤ 2 ^ w)
variable (bucketFit : (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a +
  (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a ≤ 2 ^ w)
variable (pieceFit : pieceCount (2 ^ a) (Shrink.colors a) < 2 ^ w)
variable (twoFits : 2 < 2 ^ w)
variable (owners : H.owners.eval pub state mem = q 2)
variable (reg : RowRegions q) (nrows : (q 2).val =
  (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a +
  (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a)
variable (cap : pieceCount (2 ^ a) (Shrink.colors a) ≤ (q 4).val)
local notation "b" => X.packingData.bundle m
local notation "port" => portIndex sites b
local notation "fiber" => Subtype.mk m (Eq.refl b)
local notation "piece" => X.shrinkNumber b fiber
local notation "member" => members X arcFit bucketFit b

open private row_fits from OAI.Computability.VPVNP.CompressorRecordPreimageScan
open private actual_id from OAI.Computability.VPVNP.PairShrinkABFrameAddress

include owners nrows twoFits in
private theorem half_count :
    (H.owners.div (.lit 2)).eval pub state mem = CursorRAM.encode w bundles := by
  change Fin.ofNat _ ((H.owners.eval pub state mem).val / ((2 : Word w).val)) = _
  rw [owners, nrows, show (2 : Word w).val = 2 from Nat.mod_eq_of_lt twoFits]
  rw [← Nat.mul_two, Nat.mul_div_cancel _ (by decide : 0 < 2)]

include arcFit bucketFit owners nrows twoFits stored pieceFit reg cap in
theorem candidate_eq (filled : PreimagesAt q (wordOwner (P) arcs sites) mem arcCount)
    (i : Fin pieces) :
    (H.candidate pieces i.val).eval pub state mem =
      IncidenceDirectory.actualPort X (packingInputEdges X.Base a g (member i).1.1) := by
  let v : Word w := Fin.ofNat _ (bucketIndex sites (.inr b)).val
  have vw : v.val = (bucketIndex sites (.inr b)).val :=
    Nat.mod_eq_of_lt ((bucketIndex sites (.inr b)).isLt.trans_le bucketFit)
  have below : v < q 2 := by
    change v.val < (q 2).val
    rw [vw, nrows]; exact (bucketIndex sites (.inr b)).isLt
  have bundle := (ShrinkAB.Physical.coordinates X H.fields pub state mem m stored pieceFit).1
  have base := half_count X H pub state mem twoFits owners nrows
  have index : CursorRAM.encode w bundles + CursorRAM.encode w (port).val = v := by
    exact Fin.ext (Nat.add_mod ..).symm
  change mem ((H.fields.lists.eval pub state mem + ((H.owners.div (.lit 2)).eval pub state mem +
    (H.fields.bundle pieces).eval pub state mem) * H.fields.listStride.eval pub state mem) +
    (i.val : Word w)).val = _
  rw [stored.lists, stored.listStride, base, bundle, index]
  change mem ((rowAt q v) + (i.val : Word w)).val = _
  have endRow := row_fits reg below
  have valid : (rowAt q v).val + i.val < 2 ^ w := by have := i.isLt; omega
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt valid]
  have size := arcList_length (P) arcs sites (State.two_le_packingColors a)
    arcFit bucketFit (.inr b)
  let j := Fin.cast size.symm i
  have read := (filled.rows v below).2 j
  have he := ordinalEquiv_id (P) arcs sites arcFit bucketFit (.inr b) j
  exact read.trans (he.trans (actual_id X (member i).1.1))

private theorem equal_eval (x y : Expr) :
    (equal x y).eval pub state mem =
      if x.eval pub state mem = y.eval pub state mem then 1 else 0 := by
  let z := x.eval pub state mem - y.eval pub state mem
  change 1 - (Fin.ofNat _ (z.val / z.val) : Word w) = _
  by_cases eqn : x.eval pub state mem = y.eval pub state mem
  · have hz : z = 0 := sub_eq_zero.mpr eqn
    simp [hz, eqn]
  · have hz : z ≠ 0 := fun h ↦ eqn (sub_eq_zero.mp h)
    have pos : 0 < z.val := Nat.pos_of_ne_zero (fun h ↦ hz (Fin.ext h))
    simp only [ite_eq_right eqn, Nat.div_self pos]
    exact sub_self _

private theorem sum_eval (xs : List Expr) :
    (PortRefresh.ArgumentAddress.sum xs).eval pub state mem =
      (xs.map fun e ↦ e.eval pub state mem).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x.eval pub state mem + (PortRefresh.ArgumentAddress.sum xs).eval pub state mem = _
    rw [ih]; rfl

include arcFit bucketFit owners nrows twoFits stored pieceFit reg cap in
theorem arc_eq (filled : PreimagesAt q (wordOwner (P) arcs sites) mem arcCount)
    (ranked : BundleWidthScatter.RankedInput (P) X.shrinkNumber X.shrinkOrder arcs sites s mem
      X.packingWidth) :
    (H.arc pieces).eval pub state mem =
      IncidenceDirectory.actualPort X (packingInputEdges X.Base a g m.1) := by
  let matchIndex := (member).symm fiber
  have candidate := candidate_eq X H pub state mem m stored arcFit bucketFit pieceFit
    twoFits owners reg nrows cap filled
  have rank (i : Fin pieces) :
      (Expr.load (H.fields.rankBase.add (H.candidate pieces i.val))).eval pub state mem =
        CursorRAM.encode w (X.shrinkNumber b (member i)).val := by
    change mem (H.fields.rankBase.eval pub state mem +
      (H.candidate pieces i.val).eval pub state mem).val = _
    rw [stored.rankBase, candidate, ← actual_id]
    have r := ranked.ranks (member i).1.1
    rw [BundleWidthScatter.rank_motif (P) X.shrinkNumber X.shrinkOrder (member i)] at r
    exact r
  have pieceWord := (ShrinkAB.Physical.coordinates X H.fields pub state mem m stored pieceFit).2
  have eqRank (i : Fin pieces) :
      CursorRAM.encode w (X.shrinkNumber b (member i)).val = CursorRAM.encode w (piece).val ↔
        i = matchIndex := by
    constructor
    · intro eqn
      have r := congrArg Fin.val eqn
      change (X.shrinkNumber b (member i)).val % _ = (piece).val % _ at r
      rw [Nat.mod_eq_of_lt ((X.shrinkNumber b (member i)).isLt.trans pieceFit),
        Nat.mod_eq_of_lt ((piece).isLt.trans pieceFit)] at r
      exact (member).injective (((X.shrinkNumber b).injective (Fin.ext r)).trans
        ((member).apply_symm_apply fiber).symm)
    · rintro rfl
      rw [Equiv.apply_symm_apply]
  have each (i : Fin pieces) : (H.select pieces i.val).eval pub state mem =
      if i = matchIndex then IncidenceDirectory.actualPort X (packingInputEdges X.Base a g m.1)
      else 0 := by
    change (equal _ _).eval pub state mem * (H.candidate pieces i.val).eval pub state mem = _
    rw [equal_eval, rank, pieceWord]
    by_cases hm : i = matchIndex
    · rw [ite_eq_left ((eqRank i).2 hm), one_mul, ite_eq_left hm, candidate, hm]
      simp only [matchIndex, Equiv.apply_symm_apply]
    · rw [ite_eq_right (fun h ↦ hm ((eqRank i).1 h)), zero_mul, ite_eq_right hm]
  rw [Header.arc, sum_eval, List.map_map, ← List.ofFn_id, List.map_ofFn]
  simp only [List.sum_ofFn, Function.comp_apply, id_eq, each, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]


include arcFit bucketFit owners nrows twoFits stored pieceFit reg cap in
theorem flag_eq (filled : PreimagesAt q (wordOwner (P) arcs sites) mem arcCount)
    (ranked : BundleWidthScatter.RankedInput (P) X.shrinkNumber X.shrinkOrder arcs sites s mem
      X.packingWidth) (degreeFits : d < 2 ^ w) (p : Fin 14 → Word w) (layout : Bool)
    (column : ShrinkRAM.PlacementColumns X.slots X.baseIndex p layout mem)
    (thick : H.thickness.eval pub state mem = p 11) :
    (H.flag d pieces).eval pub state mem =
      CursorRAM.encode w (ShrinkOldHalves.cDirection X m).toNat := by
  have arc := arc_eq X H pub state mem m stored arcFit bucketFit pieceFit twoFits
    owners reg nrows cap filled ranked
  have num : ((H.arc pieces).eval pub state mem).val = (arcs m.1).val := by
    rw [arc, ← actual_id, Fin.val_ofNat, Nat.mod_eq_of_lt ((arcs m.1).isLt.trans_le arcFit)]
  have site := BundleRAM.site_quotient X (CursorRAM.encode w d)
    (Nat.mod_eq_of_lt degreeFits) m.1 _ num
  change mem (H.thickness.eval pub state mem +
    ShrinkRAM.div ((H.arc pieces).eval pub state mem) (CursorRAM.encode w d)).val = _
  rw [thick, site]
  apply Fin.ext
  have bits := congrArg (Prod.fst ∘ Prod.snd) (column.atSite (sourcePosition m.1))
  change (mem (p 11 + ShrinkRAM.word w
      (Shrink.oldNumber X.baseIndex (sourcePosition m.1))).val).val =
    (ShrinkOldHalves.cDirection X m).toNat at bits
  have small : (ShrinkOldHalves.cDirection X m).toNat < 2 ^ w := by
    have bound : ∀ bit : Bool, bit.toNat ≤ 1 := by decide
    exact (bound _).trans_lt (lt_trans (by decide : 1 < 2) twoFits)
  exact bits.trans (Nat.mod_eq_of_lt small).symm

include arcFit bucketFit owners nrows twoFits stored pieceFit reg cap in
theorem field_eq (filled : PreimagesAt q (wordOwner (P) arcs sites) mem arcCount)
    (ranked : BundleWidthScatter.RankedInput (P) X.shrinkNumber X.shrinkOrder arcs sites s mem
      X.packingWidth) (degreeFits : d < 2 ^ w) (p : Fin 14 → Word w) (layout : Bool)
    (column : ShrinkRAM.PlacementColumns X.slots X.baseIndex p layout mem)
    (thick : H.thickness.eval pub state mem = p 11)
    (T : IncidenceDirectory w) (A : NodeArguments.Arena) (older stride : ℕ)
    (hs : H.fields.oldHalf.Stored T A older stride pub state mem) (cols : T.ActualColumns X mem)
    (atD : Bool) :
    let nodes := fun u ↦ older + stride * PortRefresh.ArgumentAddress.siteOrdinal X u
    (H.field d pieces atD).eval pub state mem = CursorRAM.encode w
      (ShrinkOldHalves.address X A nodes m.1
        (if atD then !(ShrinkOldHalves.cDirection X m) else ShrinkOldHalves.cDirection X m)) := by
  intro nodes
  have arc := arc_eq X H pub state mem m stored arcFit bucketFit pieceFit twoFits
    owners reg nrows cap filled ranked
  have bit := flag_eq X H pub state mem m stored arcFit bucketFit pieceFit twoFits
    owners reg nrows cap filled ranked degreeFits p layout column thick
  have field (dir : Bool) := ShrinkOldHalves.Physical.field_eq X H.fields.oldHalf T A older stride
    pub state mem hs cols arcFit degreeFits m.1 (H.arc pieces) arc dir
  let dir := ShrinkOldHalves.cDirection X m
  have flagValue : (H.flag d pieces).eval pub state mem = if dir then 1 else 0 := by
    rw [bit]
    change CursorRAM.encode w dir.toNat = if dir then 1 else 0
    cases dir <;> rfl
  have f (d' : Bool) : (H.fields.oldHalf.field d (H.arc pieces) d').eval pub state mem =
      CursorRAM.encode w (ShrinkOldHalves.address X A nodes m.1 d') := field d'
  cases atD with
  | false =>
    change (H.flag d pieces).eval pub state mem * _ + (1 - (H.flag d pieces).eval pub state mem) *
      (H.fields.oldHalf.field d (H.arc pieces) false).eval pub state mem = _
    rw [flagValue, f false, f true]
    cases hv : ShrinkOldHalves.cDirection X m <;> simp [dir, hv]
  | true =>
    change (1 - (H.flag d pieces).eval pub state mem) * _ +
      (1 - (1 - (H.flag d pieces).eval pub state mem)) *
      (H.fields.oldHalf.field d (H.arc pieces) false).eval pub state mem = _
    rw [flagValue, f false, f true]
    cases hv : ShrinkOldHalves.cDirection X m <;> simp [dir, hv]


namespace Published

/-- Read the external word at a fixed scalar offset from the runtime old-level header address. -/
def load (old : Expr) (offset : ℕ) : Expr := .load (old.add (.lit offset))

/-- Level header offsets 0, 1 and 2 give the old base, degree and lane counts.
The original bucket owner and appended-ID rectangles determine the count of
classified buckets and the preceding thickness column. -/
def header (a : ℕ) (old motif arenaBase arenaStride destination : Expr) : Header :=
  let oldSites := (load old 0).mul (load old 2)
  let oldSlots := oldSites.mul (load old 1)
  let owner := load old 44
  let ids := load old 46
  let child : ShrinkOldHalves.Physical.Header :=
    ⟨arenaBase, arenaStride, load old 14, load old 15, load old 57, load old 58, load old 59⟩
  let ab : ShrinkAB.Physical.Header :=
    ⟨child, motif, ids, .lit (ShrinkRankSpace.cap a), load old 45, load old 43, destination⟩
  ⟨ab, ids.sub (owner.add ((Expr.lit 2).mul oldSlots)), owner.sub ((Expr.lit 3).mul oldSites)⟩

variable (old motif arenaBase arenaStride destination : Expr)
local notation "hdr" => header a old motif arenaBase arenaStride destination
variable (start : ℕ) (T : IncidenceDirectory w)
local notation "plan" => ShrinkInput.plan X start
local notation "collect" => ShrinkRankSpace.Shape.collectBank plan w
local notation "placement" => ShrinkInput.placementBank X T start

/-- Resolve both calculated heads to the values that the shrinking scan
actually published into its bucket and preliminary placement operand banks. -/
theorem geometry
    (vertices : (load old 0).eval pub state mem = (Fintype.card X.Base : Word w))
    (degree : (load old 1).eval pub state mem = ((2 ^ a : ℕ) : Word w))
    (lanes : (load old 2).eval pub state mem = ((2 ^ (packingLaneBits a g) : ℕ) : Word w))
    (owner : (load old 44).eval pub state mem = ((plan).owner : Word w))
    (ids : (load old 46).eval pub state mem = ((plan).ids : Word w)) :
    (hdr).owners.eval pub state mem = (collect) 2 ∧
      (hdr).thickness.eval pub state mem = (placement) 11 := by
  constructor
  · change (load old 46).eval pub state mem - ((load old 44).eval pub state mem +
      2 * ((load old 0).eval pub state mem * (load old 2).eval pub state mem *
        (load old 1).eval pub state mem)) = _
    rw [ids, owner, vertices, degree, lanes]
    change (((plan).owner + 2 * (plan).A + 2 * (plan).B : ℕ) : Word w) -
      ((plan).owner + 2 * ((Fintype.card X.Base : Word w) * ↑(2 ^ packingLaneBits a g : ℕ) *
        ↑(2 ^ a : ℕ))) = ↑(2 * (plan).B : ℕ)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ShrinkRankSpace.Shape.A,
      ShrinkRankSpace.slots, ShrinkInput.plan, ShrinkRankArena.shape]
    ring
  · change (load old 44).eval pub state mem - 3 *
      ((load old 0).eval pub state mem * (load old 2).eval pub state mem) = _
    rw [owner, vertices, lanes]
    change ((ShrinkInput.placementBase X start + 4 *
      (Fintype.card X.Base * 2 ^ (packingLaneBits a g)) : ℕ) : Word w) - 3 *
      ((Fintype.card X.Base : Word w) * ↑(2 ^ packingLaneBits a g : ℕ)) =
      ↑(ShrinkInput.placementBase X start + 1 * (Fintype.card X.Base *
        2 ^ packingLaneBits a g) : ℕ)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

/-- The physical child field expressions use the published old DFS geometry
and the incidence heads following the 54-word scalar header. -/
theorem child (A : NodeArguments.Arena) (layer stride : ℕ)
    (baseWord : arenaBase.eval pub state mem = CursorRAM.encode w A.start)
    (strideWord : arenaStride.eval pub state mem = CursorRAM.encode w A.stride)
    (layerWord : (load old 14).eval pub state mem = CursorRAM.encode w layer)
    (rowStride : (load old 15).eval pub state mem = CursorRAM.encode w stride)
    (outgoing : (load old 57).eval pub state mem = T.actualOut)
    (incoming : (load old 58).eval pub state mem = T.actualIn)
    (width : (load old 59).eval pub state mem = T.width) :
    (hdr).fields.oldHalf.Stored T A layer stride pub state mem :=
  ⟨baseWord, strideWord, layerWord, rowStride, outgoing, incoming, width⟩

/-- The raw rank, ID and AB bank heads in the old header select the
corresponding ranked input and physical copy setup. -/
theorem abHeader (bankBase target : ℕ)
    (motifWord : (motif.eval pub state mem).val = (ShrinkMotifOrder.stateNumber X m).val)
    (listWord : (load old 46).eval pub state mem = ((plan).ids : Word w))
    (rankWord : (load old 45).eval pub state mem = ((plan).ranks : Word w))
    (banks : (load old 43).eval pub state mem = CursorRAM.encode w bankBase)
    (targetWord : destination.eval pub state mem = CursorRAM.encode w target) :
    let ranks := ShrinkWidthArena.scatterBank T collect ((plan).ranks : Word w)
      (ShrinkInput.widthBase X start)
    (hdr).fields.Stored X pub state mem collect ranks bankBase target m :=
  ⟨motifWord, listWord, rfl, rankWord, banks, targetWord⟩

end Published

end PairSimulation.ShrinkCD

end VPVNP
end Computability
end OAI

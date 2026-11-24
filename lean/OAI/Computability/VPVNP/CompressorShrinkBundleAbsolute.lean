import OAI.Computability.VPVNP.CompressorShrinkBundlePlan

/-!
# Installing absolute motif identifiers after the width and AB scans

The old gathered-key rectangle is available after ranking. The final scan
reads the retained classifier keys, owners and ranks, and replaces the two
halves of this rectangle with the thick auxiliary words and dense CD arc IDs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBundlePlan

open BurstRAM PrimedStackRAM Compression Compression.PackingData BundleKeys BundleWidthScatter
open scoped Classical Fin.CommRing
open private offset_lt from OAI.Computability.VPVNP.CompressorRecordsBundleWidthScatter

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : ShrinkInput.Run X T start m)

local notation "Z" => ShrinkInput.plan X start
local notation "A" => ShrinkRankSpace.Shape.A (ShrinkInput.plan X start)
local notation "B" => ShrinkRankSpace.Shape.B (ShrinkInput.plan X start)
local notation "Q" => ShrinkRankSpace.Shape.Q (ShrinkInput.plan X start)
local notation "p" => absoluteBank Z w
local notation "cols" => MotifAbsolute.columns (absoluteBank Z w)
local notation "arcOrder" => BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex

/-- The first absolute CD motif-ID address in the second half of the reused gathered-key
rectangle. -/
def absoluteHead (z : ShrinkRankSpace.Shape) (w : ℕ) : Word w := Fin.ofNat _ (z.gathered+z.B*z.Q)

/-- The old classifier and rank cells still contain the data for each original
outgoing port. The width and AB stages all ran above these addresses. -/
theorem absolute_inputs (fit : (Z).stop < 2^w) :
    MotifAbsolute.Inputs X.slots X.baseIndex p r.post X.shrinkNumber X.shrinkOrder := by
  have val := (Z).values T (ShrinkInput.placementBank X T start) Fintype.card_pos fit
  have space := absolute_layout X (start := start) fit
  have endBefore (t : Fin 3) : (cols (t.castAdd 2)).val+A ≤ ShrinkInput.widthBase X start := by
    change _ ≤ (Z).ranks+A
    fin_cases t
    · change (Fin.ofNat (2^w) (Z).owner).val+A ≤ _
      rw [show (Fin.ofNat (2^w) (Z).owner).val = _ from val.owner]
      apply Nat.add_le_add_right
      unfold ShrinkRankSpace.Shape.owner ShrinkRankSpace.Shape.ranks ShrinkRankSpace.Shape.gathered
        ShrinkRankSpace.Shape.ids ShrinkRankSpace.Shape.counts
      omega
    · change (Fin.ofNat (2^w) (Z).ranks).val+A ≤ _
      rw [val.ranks]
    · change (Fin.ofNat (2^w) (Z).key).val+A ≤ _
      rw [show (Fin.ofNat (2^w) (Z).key).val = _ from val.key]
      apply Nat.add_le_add_right
      unfold ShrinkRankSpace.Shape.key ShrinkRankSpace.Shape.ranks ShrinkRankSpace.Shape.gathered
        ShrinkRankSpace.Shape.ids ShrinkRankSpace.Shape.counts
      omega
  have read (t : Fin 3) (e : OldArc X.Base a g) :
      r.post (source cols t (arcWord arcOrder e)).val =
        r.rankPost ((cols (t.castAdd 2)).val + (arcOrder e).val) := by
    have hi : (arcOrder e).val < A := (arcOrder e).isLt
    have hb := endBefore t
    have hr := space.sourceFits t
    rw [source,arcWord,Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by omega)]
    exact r.afterRank _ (by omega)
  constructor
  · intro e; rw [read]
    exact r.ranking.owners e
  · intro e; rw [read]
    by_cases h : X.packingData.thick (sourcePosition e) ∧ X.packingData.thick (sourcePosition (X.packingData.actual e))
    · let x : X.packingData.ThickFiber e.1 := ⟨⟨e,h⟩,rfl⟩
      rw [show rankOf X.packingData X.shrinkNumber X.shrinkOrder e = (X.shrinkOrder e.1 x).val from
        rank_thick X.packingData X.shrinkNumber X.shrinkOrder x]
      exact r.ranking.thick _ x
    · let y : X.packingData.Motif := ⟨e,h⟩
      let x : X.packingData.MotifFiber (X.packingData.bundle y) := ⟨y,rfl⟩
      rw [show rankOf X.packingData X.shrinkNumber X.shrinkOrder e = (X.shrinkNumber _ x).val from
        rank_motif X.packingData X.shrinkNumber X.shrinkOrder x]
      exact r.ranking.motifs _ x
  · intro e; rw [read]
    have hk := r.ranking.ranked.keys e.val
    rw [show BundleRAM.bothThick X.slots X.baseIndex e.val = false from decide_eq_false e.property] at hk
    exact hk

/-- Native absolute-ID scan, its exact charge, and the interval containing all writes. -/
structure AbsoluteRun (rs : List (Report w)) : Prop where
  native : runSegment ((template MotifAbsolute.visit 0).instantiate w p).program 25 (some 0) r.post
    (List.replicate A []) = some rs
  cursor : endState (some 0) rs = some (Fin.ofNat _ A)
  count : rs.length = A
  work : ∀ z ∈ rs, z.events.length = 24 ∧ z.probes = 4
  charge : RAMBuckets.cost Report.probes rs = 5*A
  directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber (absoluteHead Z w)
    (after r.post (eventLog rs))
  frame : ∀ j, j < (Z).gathered ∨ (Z).ranks ≤ j → after r.post (eventLog rs) j = r.post j

theorem run_absolute (fit : (Z).stop < 2^w) : ∃ rs, AbsoluteRun r rs := by
  have layout := absolute_layout X (start := start) fit
  have hinput := absolute_inputs r fit
  have hv := (Z).values T (ShrinkInput.placementBank X T start) Fintype.card_pos fit
  have scalars := (Z).scalarFits Fintype.card_pos fit
  have hd : (p 5).val = 2^a := Nat.mod_eq_of_lt scalars.2.2.2.1
  have hl : (p 6).val = 2^g := Nat.mod_eq_of_lt scalars.2.2.2.2.1
  have stride : (cols 3).val = Q := hv.stride
  have out : (cols 4).val = (Z).gathered := hv.gathered
  have rect : (Z).gathered+(B+B)*Q = (Z).ranks := by
    change (Z).gathered+(B+B)*Q = (Z).gathered+(2*B)*Q
    rw [two_mul]
  have room : (Z).ranks+A < 2^w := fit
  have hhead : (absoluteHead Z w).val = (cols 4).val+B*Q := by
    rw [out]
    have h := Nat.le_add_left (B*Q) (B*Q)
    rw [Nat.add_mul] at rect
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rs,hn,he,hf,hc,hw,charge,dir⟩ := MotifAbsolute.graph_run X.slots X.baseIndex
    p r.post X.shrinkNumber X.shrinkOrder (absoluteHead Z w) layout hd hl stride hhead hinput
  refine ⟨rs,hn,he,hc,hw,charge,dir,?_⟩
  let old := fun e ↦ (BundleWidthScatter.width cols r.post (arcWord arcOrder e)).val
  have ranked : RankedInput X.packingData X.shrinkNumber X.shrinkOrder arcOrder sites cols r.post old :=
    ⟨hinput.owners,hinput.ranks,fun _ ↦ rfl⟩
  intro addr ha
  apply hf.frame
  intro i hi
  let e := (arcOrder).symm ⟨i,hi⟩
  have he : (arcOrder e).val = i := congrArg Fin.val ((arcOrder).apply_symm_apply _)
  have eqn := output_eq X.packingData X.shrinkNumber X.shrinkOrder arcOrder sites layout ranked e
  have bound := offset_lt X.packingData X.shrinkNumber X.shrinkOrder sites layout e
  unfold arcWord at eqn
  rw [he,out,stride] at eqn
  rw [stride] at bound
  change _ < (B+B)*Q at bound
  omega

/-- A later demand gather or term selector preserves the absolute IDs by
preserving memory below the shrinking input endpoint. -/
theorem AbsoluteRun.directory_after {rs : List (Report w)} (h : AbsoluteRun r rs) {out : Memory w}
    (frame : ∀ j < ShrinkInput.stop X start, out j = after r.post (eventLog rs) j) :
    MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber (absoluteHead Z w) out := by
  intro i
  have hi : i.val < B*Q := i.isLt
  have head : (absoluteHead Z w).val ≤ (Z).gathered+B*Q := Nat.mod_le ..
  have top : (Z).gathered+B*Q+B*Q = (Z).ranks := by
    change (Z).gathered+B*Q+B*Q = (Z).gathered+(2*B)*Q
    rw [two_mul,Nat.add_mul,Nat.add_assoc]
  have last : (Z).ranks ≤ ShrinkInput.stop X start := by
    change (Z).ranks ≤ (Z).ranks+A+6*(B*Q)+2*B
    omega
  rw [frame _ (by omega)]
  exact h.directory i

end CompressorRecords.ShrinkBundlePlan

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.PairShrinkCallHeader
import OAI.Computability.VPVNP.PairShrinkArgumentReadBounds

/-!
# Addresses read by the CD rank scan

The native expression tests every old arc in the second classified row for
the selected bundle. Each candidate read stays in the ID rectangle, each
rank read stays in the old-arc rank column, and the thickness test stays in
the old-site column. Both possible child addresses use the original
incidence columns and the full fixed-degree width prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCDReadBounds

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData CompressorRecords
open CompressorRecords.PhaseRecipe CompressorRecords.BundleLists
open scoped Fin.CommRing

open private half_count from OAI.Computability.VPVNP.PairShrinkCDFieldAddress
open private actual_id from OAI.Computability.VPVNP.PairShrinkABFrameAddress
open private rowAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan

variable {a g w : ℕ} (X : State a (packingLaneBits a g))
variable (m : X.packingData.Motif) (C : ShrinkCD.Header)
variable {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}
variable (H : ℕ) (T : IncidenceDirectory w) (origin : ℕ)
local notation "P" => X.packingData
local notation "d" => 2 ^ a
local notation "Q" => pieceCount d (Shrink.colors a)
local notation "sites" => Fintype.card X.Base * 2 ^ (packingLaneBits a g)
local notation "N" => sites * d
local notation "B" => (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * d
local notation "Z" => ShrinkInput.plan X origin
local notation "q" => ShrinkRankSpace.Shape.collectBank Z w
local notation "rank" => ShrinkWidthArena.scatterBank T q
  (CursorRAM.encode w (ShrinkRankSpace.Shape.ranks Z)) (ShrinkInput.widthBase X origin)
local notation "pre" => ShrinkInput.placementBank X T origin
local notation "ev" => Expr.eval pub state mem
local notation "rd" => Expr.ReadsFrom (· < H) pub state mem
/-- Classical equality on the input base vertices for tracing the CD row and incidence reads. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Readable source expressions for the row classifier and rank scan. -/
structure ScanInputs (C : ShrinkCD.Header) (H : ℕ) (pub : Fin 5 → Word w) (state : Word w)
    (mem : Memory w) : Prop where
  owners : C.owners.ReadsFrom (· < H) pub state mem
  lists : C.fields.lists.ReadsFrom (· < H) pub state mem
  motif : C.fields.motif.ReadsFrom (· < H) pub state mem
  stride : C.fields.listStride.ReadsFrom (· < H) pub state mem
  ranks : C.fields.rankBase.ReadsFrom (· < H) pub state mem
  thickness : C.thickness.ReadsFrom (· < H) pub state mem

private theorem add_lt (x y : Word w) (h : x.val + y.val < H) : (x + y).val < H :=
  (Nat.mod_le ..).trans_lt h

private theorem sum_reads (xs : List Expr) (each : ∀ x ∈ xs, rd x) :
    rd (PortRefresh.ArgumentAddress.sum xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨each x List.mem_cons_self,
      ih (fun e he ↦ each e (List.mem_cons_of_mem _ he))⟩

/-- Confinement of all candidate and rank probes, including the candidates
whose ranks fail the test. -/
theorem scan {first dest : ℕ} (safe : ScanInputs C H pub state mem)
    (stored : C.fields.Stored X pub state mem q rank first dest m)
    (geometry : ShrinkCallHeader.Geometry (w := w) X origin)
    (owners : ev C.owners = q 2) (thick : ev C.thickness = pre 11)
    (old : ShrinkCallHeader.OldTables X mem T origin) (twoFits : 2 < 2 ^ w)
    (space : (Z).stop < 2 ^ w) (endBefore : (Z).stop ≤ H) :
    rd (C.arc Q) ∧ rd (C.flag d Q) := by
  let port := portIndex (Shrink.packedIndex (a := a) (g := g) X.baseIndex) ((P).bundle m)
  let v := CursorRAM.encode w (B + port.val)
  have portLt : port.val < B := port.isLt
  have vw : v.val = B + port.val := Nat.mod_eq_of_lt (by have := geometry.bucketFit; omega)
  have below : v < q 2 := by change v.val < (q 2).val; rw [vw, geometry.nrows]; omega
  have bundle := (ShrinkAB.Physical.coordinates X C.fields pub state mem m stored
    geometry.piecesFit).1
  have half := half_count X C pub state mem twoFits owners geometry.nrows
  have values := (Z).values T pre Fintype.card_pos space
  have rowRoom : (q 5).val + (q 2).val * (q 4).val ≤ H := by
    rw [values.ids, values.buckets, values.stride]
    change (Z).gathered ≤ H
    have h₁ : (Z).gathered ≤ (Z).ranks := Nat.le_add_right _ _
    have h₂ : (Z).ranks ≤ (Z).stop := Nat.le_add_right _ _
    exact h₁.trans (h₂.trans endBefore)
  have candidate (i : Fin Q) : rd (C.candidate Q i.val) := by
    refine ⟨⟨⟨safe.lists, ⟨⟨safe.owners, trivial⟩, safe.motif, trivial⟩, safe.stride⟩,
      trivial⟩, ?_⟩
    change ((ev C.fields.lists + ((ev (C.owners.div (.lit 2))) +
      ev (C.fields.bundle Q)) * ev C.fields.listStride) + (i.val : Word w)).val < H
    rw [stored.lists, half, bundle, stored.listStride]
    have index : CursorRAM.encode w B + CursorRAM.encode w port.val = v :=
      Fin.ext (Nat.add_mod ..).symm
    rw [index]
    change (rowAt q v + (i.val : Word w)).val < H
    apply add_lt H
    rw [rowAt_val geometry.regions below]
    have indexFits := (Nat.mod_le i.val (2 ^ w)).trans_lt (i.isLt.trans_le geometry.cap)
    have step := Nat.mul_le_mul_right (q 4).val (show v.val + 1 ≤ (q 2).val from below)
    rw [Nat.succ_mul] at step
    change (q 5).val + v.val * (q 4).val + i.val % (2 ^ w) < H
    omega
  have id (i : Fin Q) := ShrinkCD.candidate_eq X C pub state mem m stored geometry.arcFit
    geometry.bucketFit geometry.piecesFit twoFits owners geometry.regions geometry.nrows
    geometry.cap old.preimages i
  have rankRead (i : Fin Q) : rd (.load (C.fields.rankBase.add (C.candidate Q i.val))) := by
    refine ⟨⟨safe.ranks, candidate i⟩, ?_⟩
    change (ev C.fields.rankBase + ev (C.candidate Q i.val)).val < H
    rw [stored.rankBase, id, ← actual_id]
    apply add_lt H
    change (Fin.ofNat (2 ^ w) (Z).ranks).val + _ < H
    rw [values.ranks]
    let ord := BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
    have atRank (e : BundleKeys.OldArc X.Base a g) :
        (Z).ranks + (Fin.ofNat (2 ^ w) (ord e).val).val < H :=
      (Nat.add_lt_add_left ((Nat.mod_le ..).trans_lt (ord e).isLt) _).trans_le endBefore
    exact atRank ((ShrinkCD.members X geometry.arcFit geometry.bucketFit ((P).bundle m) i).1.1)
  have select (i : Fin Q) : rd (C.select Q i.val) := by
    let diff := (Expr.load (C.fields.rankBase.add (C.candidate Q i.val))).sub (C.fields.piece Q)
    have diffRead : rd diff := ⟨rankRead i, safe.motif, trivial⟩
    exact ⟨⟨trivial, diffRead, diffRead⟩, candidate i⟩
  have arcRead : rd (C.arc Q) := by
    apply sum_reads H
    intro e he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    exact select i
  refine ⟨arcRead, ⟨⟨safe.thickness, arcRead, trivial⟩, ?_⟩⟩
  change (ev C.thickness + BinaryOp.div.eval (ev (C.arc Q)) ((2 ^ a : ℕ) : Word w)).val < H
  rw [thick, ShrinkCD.arc_eq X C pub state mem m stored geometry.arcFit geometry.bucketFit
    geometry.piecesFit twoFits owners geometry.regions geometry.nrows geometry.cap
    old.preimages old.ranked, ← actual_id]
  apply add_lt H
  let ord := BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
  have small : (ord m.1).val % (2 ^ w) / d < sites :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a)).2 ((Nat.mod_le ..).trans_lt (ord m.1).isLt)
  have base : (pre 11).val ≤ ShrinkInput.placementBase X origin + sites := by
    change (_ + 1 * sites) % (2 ^ w) ≤ _
    simpa only [one_mul] using Nat.mod_le (ShrinkInput.placementBase X origin + sites) (2 ^ w)
  have ready : (pre 11).val + sites ≤ H := by
    have h := (ShrinkInput.range_bounds X origin).2.2.1
    change ShrinkInput.placementBase X origin + 4 * sites ≤ (Z).stop at h
    omega
  change (pre 11).val + ((ord m.1).val % (2 ^ w) / (d % (2 ^ w))) % (2 ^ w) < H
  rw [Nat.mod_eq_of_lt geometry.degreeFit]
  exact (Nat.add_lt_add_left ((Nat.mod_le ..).trans_lt small) _).trans_le ready

end PairSimulation.ShrinkCDReadBounds

end VPVNP
end Computability
end OAI

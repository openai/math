import OAI.Computability.VPVNP.PairShrinkCallFields
import OAI.Computability.VPVNP.PairShrinkCDFieldAddress
import OAI.Computability.VPVNP.CompressorShrinkInputTerms

/-!
# Reading the selected shrink map header

The physical level contains a term head, a ten-word row stride, the selected
layout and the dense AB/CD pair head. The number of private hidden slots
comes from the actual base and residual lane counts of this level. Reading
the classified CD row and its source-thickness flag supplies the direct
pointers at C and D, including when the independent half-words disagree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallHeader

open Compression Compression.PackingData Compression.ShrinkMotif CompressorRecords
open BurstRAM BurstRAM.PrivateRAM CompressorRecords.PhaseRecipe
open MotifGrid MotifBlocks MotifConversion
open scoped Fin.CommRing

/-- Live register expressions on entry to one resident map. -/
structure Operands where
  /-- External address of the selected old-level header. -/
  level : Expr
  /-- Dense ordinal selecting this motif's term and row in the shrinking tables. -/
  motif : Expr
  /-- Private start address of the argument frames indexed by absolute DFS node. -/
  arguments : Expr
  /-- Number of private words reserved between consecutive node argument frames. -/
  argumentStride : Expr
  /-- Start of the private shared supply-field slots, indexed by motif and role. -/
  hidden : Expr
  /-- Distance in private words between adjacent shared or staged supply fields. -/
  slotStride : Expr
  /-- Private address of the histogram to which the evaluated map contributes. -/
  hist : Expr

/-- Read a scalar or table pointer at the specified offset from the old-level header. -/
def Operands.cell (O : Operands) (i : ℕ) := ShrinkCD.Published.load O.level i

/-- The dense motif count is the product of absolute bundle count and piece count. -/
def Operands.count (O : Operands) (a : ℕ) : Expr :=
  (((O.cell 0).mul ((Expr.lit (2 ^ (Shrink.J a))).mul (O.cell 3))).mul (.lit (2 ^ a))).mul
    (.lit (pieceCount (2 ^ a) (Shrink.colors a)))

/-- First private staging word after the four shared slots reserved for each motif. -/
def Operands.staging (O : Operands) (a : ℕ) : Expr :=
  O.hidden.add (((Expr.lit 4).mul (O.count a)).mul O.slotStride)

/-- Assemble the published CD lookup expressions from the selected level, motif ordinal, old
argument geometry, and staging address. -/
def Operands.cdHeader (O : Operands) (a : ℕ) : ShrinkCD.Header :=
  ShrinkCD.Published.header a O.level O.motif O.arguments O.argumentStride (O.staging a)

/-- Build the map-field recipe, including the dynamic motif count and the oriented CD source
addresses at the old degree. -/
def Operands.inputs (O : Operands) (a : ℕ) : ShrinkCallFields.Inputs :=
  ⟨O.level, O.motif, O.hidden, O.slotStride, O.count a, O.hist,
    (O.cdHeader a).field (2 ^ a) (pieceCount (2 ^ a) (Shrink.colors a))⟩

variable {a g w : ℕ} (X : State a (packingLaneBits a g))
variable {k : Type*} [_root_.Field k] {factor : ℝ}
variable (F : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (sel : X.ShrinkSelection F) (m : X.packingData.Motif)
/-- Classical equality on old base vertices for interpreting the selected motif's native field
and bundle pointers. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "P" => X.packingData
local notation "d" => 2 ^ a
local notation "c" => Shrink.colors a
local notation "Q" => pieceCount d c
local notation "arcs" => BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "arcCount" => Fintype.card X.Base * 2 ^ (packingLaneBits a g) * d
local notation "bundleCount" => (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * d
local notation "side" => X.packingData.shrinkTermLayout F X.shrinkNumber X.packingWidth sel
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)

variable (O : Operands) (pub : Fin 5 → Word w) (state level : Word w) (mem : Memory w)
local notation "ev" => Expr.eval pub state mem

/-- The private frame reserves four shared words per motif before the staged
AB and surviving endpoints. -/
def scratch (hidden stride hist : ℕ) : ShrinkCallFields.Scratch :=
  ⟨hidden, stride, ShrinkTermInputs.motifCount X, hist⟩

variable (A : NodeArguments.Arena) (T : IncidenceDirectory w) (origin older stride bankBase : ℕ)
variable (hidden slotStride hist : ℕ)
local notation "plan" => ShrinkInput.plan X origin
local notation "q" => ShrinkRankSpace.Shape.collectBank plan w
local notation "rank" => ShrinkWidthArena.scatterBank T q
  (CursorRAM.encode w (ShrinkRankSpace.Shape.ranks plan)) (ShrinkInput.widthBase X origin)
local notation "pre" => ShrinkInput.placementBank X T origin
local notation "term" => ShrinkInput.termHead (w := w) X origin
local notation "dense" => ShrinkInput.demandHead (w := w) X origin
local notation "heap" => scratch X hidden slotStride hist

/-- The scalar slots and graph-array heads of the actual old level, read as
machine words at their offsets in the published header. -/
structure Level : Prop where
  vertices : mem (level + 0).val = (Fintype.card X.Base : Word w)
  degree : mem (level + 1).val = ((2 ^ a : ℕ) : Word w)
  lanes : mem (level + 2).val = ((2 ^ packingLaneBits a g : ℕ) : Word w)
  residual : mem (level + 3).val = ((2 ^ g : ℕ) : Word w)
  oldLayer : mem (level + 14).val = (older : Word w)
  rowStride : mem (level + 15).val = (stride : Word w)
  termHead : mem (level + 36).val = term
  termStride : mem (level + 37).val = 10
  layout : mem (level + 38).val = ((side).toNat : Word w)
  abBank : mem (level + 43).val = (bankBase : Word w)
  owner : mem (level + 44).val = ((plan).owner : Word w)
  rankHead : mem (level + 45).val = ((plan).ranks : Word w)
  ids : mem (level + 46).val = ((plan).ids : Word w)
  demandHead : mem (level + 47).val = dense
  actualOut : mem (level + 57).val = T.actualOut
  actualIn : mem (level + 58).val = T.actualIn
  width : mem (level + 59).val = T.width

/-- The incoming recipe expressions evaluate to the selected level, motif ordinal, argument
arena, scratch geometry, and histogram address. -/
structure Live : Prop where
  header : ev O.level = level
  motif : (ev O.motif).val = idx
  arguments : ev O.arguments = (A.start : Word w)
  argumentStride : ev O.argumentStride = (A.stride : Word w)
  hiddenBase : ev O.hidden = (hidden : Word w)
  stride : ev O.slotStride = (slotStride : Word w)
  histogram : ev O.hist = (hist : Word w)

/-- Retained source data from the original port classifier, ranker, and
preliminary placement pass in the memory on which this resident executes. -/
structure OldTables : Prop where
  preimages : PreimagesAt q (BundleLists.wordOwner (P) arcs sites) mem arcCount
  ranked : BundleWidthScatter.RankedInput (P) X.shrinkNumber X.shrinkOrder arcs sites rank mem
    X.packingWidth
  incidence : T.ActualColumns X mem
  thickness : ShrinkRAM.PlacementColumns X.slots X.baseIndex pre false mem

private theorem word_of_val {v : Word w} {n : ℕ} (h : v.val = n) : v = (n : Word w) := by
  subst n
  exact Fin.ext (Nat.mod_eq_of_lt v.isLt).symm

private theorem cell_eq (head : ev O.level = level) (i : ℕ) :
    ev (O.cell i) = mem (level + (i : Word w)).val := by
  change mem (ev O.level + (i : Word w)).val = _
  rw [head]

theorem count_eq (base : ev (O.cell 0) = (Fintype.card X.Base : Word w))
    (lanes : ev (O.cell 3) = ((2 ^ g : ℕ) : Word w)) :
    ev (O.count a) = (ShrinkTermInputs.motifCount X : Word w) := by
  rw [ShrinkTermSelection.motifCount_eq X]
  change ev (O.cell 0) * (((2 ^ (Shrink.J a) : ℕ) : Word w) * ev (O.cell 3)) *
    ((2 ^ a : ℕ) : Word w) * (Q : Word w) = _
  rw [base, lanes, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul]

/-- Natural address of the old CD half used at C or D, with orientation determined by the
motif's old source thickness. -/
noncomputable def cdBase (atD : Bool) : ℕ :=
  ShrinkOldHalves.address X A (fun u ↦ older + stride * PortRefresh.ArgumentAddress.siteOrdinal X u)
    m.1 (if atD then !(ShrinkOldHalves.cDirection X m) else ShrinkOldHalves.cDirection X m)

variable (levelData : Level X F sel level mem T origin older stride bankBase)
variable (live : Live X m O pub state level mem A hidden slotStride hist)
variable (old : OldTables X mem T origin)

/-- Pointer expressions shared by the unsplit CD read and the AB frame scan. -/
structure Heads : Prop where
  ab : (O.cdHeader a).fields.Stored X pub state mem q rank bankBase (heap).staging m
  child : (O.cdHeader a).fields.oldHalf.Stored T A older stride pub state mem
  owners : ev (O.cdHeader a).owners = q 2
  thickness : ev (O.cdHeader a).thickness = pre 11
  motifs : ev (O.count a) = (ShrinkTermInputs.motifCount X : Word w)

include levelData live in
theorem heads :
    Heads X m O pub state mem A T origin older stride bankBase hidden slotStride hist := by
  have cell := cell_eq O pub state level mem live.header
  have vertices := (cell 0).trans levelData.vertices
  have deg := (cell 1).trans levelData.degree
  have lanes := (cell 2).trans levelData.lanes
  have motifs := count_eq X O pub state mem vertices ((cell 3).trans levelData.residual)
  have stage : ev (O.staging a) = ((heap).staging : Word w) := by
    change ev O.hidden + 4 * ev (O.count a) * ev O.slotStride = _
    rw [live.hiddenBase, motifs, live.stride]
    simp [scratch, ShrinkCallFields.Scratch.staging]
  have ab := ShrinkCD.Published.abHeader X pub state mem m O.level O.motif O.arguments
    O.argumentStride (O.staging a) origin T bankBase (heap).staging live.motif
    ((cell 46).trans levelData.ids) ((cell 45).trans levelData.rankHead)
    ((cell 43).trans levelData.abBank) stage
  have child := ShrinkCD.Published.child (a := a) pub state mem O.level O.motif O.arguments
    O.argumentStride (O.staging a) T A older stride live.arguments live.argumentStride
    ((cell 14).trans levelData.oldLayer) ((cell 15).trans levelData.rowStride)
    ((cell 57).trans levelData.actualOut) ((cell 58).trans levelData.actualIn)
    ((cell 59).trans levelData.width)
  obtain ⟨owners, thick⟩ := ShrinkCD.Published.geometry X pub state mem O.level O.motif O.arguments
    O.argumentStride (O.staging a) origin T vertices deg lanes ((cell 44).trans levelData.owner)
    ((cell 46).trans levelData.ids)
  exact ⟨ab, child, owners, thick, motifs⟩

/-- Representability of the ranker's old ID and bucket arrays follows from
the allocated end of the ranking stage. -/
structure Geometry : Prop where
  arcFit : arcCount ≤ 2 ^ w
  bucketFit : bundleCount + bundleCount ≤ 2 ^ w
  piecesFit : Q < 2 ^ w
  degreeFit : d < 2 ^ w
  regions : RowRegions q
  nrows : (q 2).val = bundleCount + bundleCount
  cap : Q ≤ (q 4).val

include T in
theorem geometry (space : (plan).stop < 2 ^ w) : Geometry (w := w) X origin := by
  have ⟨arcFits, bucketsFit, piecesFit, degreeFits, _⟩ := (plan).scalarFits Fintype.card_pos space
  have bounded := (plan).values T pre Fintype.card_pos space
  have rowRegions : RowRegions q := by
    have own : (q 1).val = (plan).owner := bounded.owner
    constructor
    · rw [own, bounded.count, bounded.counts]
      change (plan).origin + (plan).A ≤ (plan).origin + 2 * (plan).A
      omega
    · rw [bounded.counts, bounded.buckets, bounded.ids]
      exact le_rfl
    · rw [bounded.ids, bounded.buckets, bounded.stride]
      change (plan).gathered ≤ 2 ^ w
      exact le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) space.le)
  have bucketFits : bundleCount + bundleCount ≤ 2 ^ w := by
    change 2 * bundleCount < _ at bucketsFit
    omega
  have nr : (q 2).val = bundleCount + bundleCount := by
    change (2 * bundleCount) % (2 ^ w) = bundleCount + bundleCount
    rw [Nat.mod_eq_of_lt (show 2 * bundleCount < 2 ^ w from bucketsFit), two_mul]
  exact ⟨arcFits.le, bucketFits, piecesFit, degreeFits, rowRegions, nr, bounded.stride.ge⟩

include levelData live old in
theorem stored (space : (plan).stop < 2 ^ w) (twoFits : 2 < 2 ^ w) :
    ShrinkCallFields.Stored pub state mem X m (O.inputs a) heap term dense 10 side
      (cdBase X m A older stride) := by
  have h := heads X F sel m O pub state level mem A T origin older stride bankBase
    hidden slotStride hist levelData live
  have G := geometry X T origin space
  have cell := cell_eq O pub state level mem live.header
  refine ⟨word_of_val live.motif, live.hiddenBase, live.stride, h.motifs, live.histogram,
    (cell 36).trans levelData.termHead, (cell 37).trans levelData.termStride,
    (cell 38).trans levelData.layout, (cell 47).trans levelData.demandHead, fun dir ↦ ?_⟩
  exact ShrinkCD.field_eq X (O.cdHeader a) pub state mem m h.ab G.arcFit G.bucketFit G.piecesFit
    twoFits h.owners G.regions G.nrows G.cap old.preimages old.ranked G.degreeFit pre false
    old.thickness h.thickness T A older stride h.child old.incidence dir


include levelData live old in
/-- The exact descriptor value for every field of the selected resident map. -/
theorem fields_eval (space : (plan).stop < 2 ^ w) (twoFits : 2 < 2 ^ w)
    (room : ShrinkInput.termEnd X origin 10 < 2 ^ w)
    (pair : ShrinkTermInputs.statePairs X dense mem)
    (record : TermRecordScan.Fields F ShrinkSliceArrays.supplyRoles demandMass_pos
      ((P).shrinkDemandWidths X.shrinkNumber X.packingWidth m) (sel m).val
      (ShrinkTermSelection.rowBase X term 10 m) mem) (j : Fin 6) (arg : ShrinkCallFields.Arg) :
    ev ((O.inputs a).fields j arg) = ShrinkCallFields.values X F sel m heap j side
      (cdBase X m A older stride) arg := by
  have h := stored X F sel m O pub state level mem A T origin older stride bankBase
    hidden slotStride hist levelData live old space twoFits
  have bounds := ShrinkInput.termLayout X T origin 10 room
  have maxI : idx < ShrinkTermInputs.motifCount X := (ShrinkMotifOrder.entries X).symm m |>.isLt
  apply ShrinkCallFields.fields_eval (O.inputs a) heap term dense 10 side
    (cdBase X m A older stride) h pair record _ _ j arg
  · have := bounds.2.2.1
    have := (term).isLt
    omega
  · have := bounds.2.2.2
    omega


local notation "ord" => BundleLists.portIndex sites (X.packingData.bundle m)
local notation "count" => 2 ^ c * d / 4
local notation "bank" => ShrinkABSliceTable.bank (w := w) bankBase count Q (Fin.val ord)

include levelData live old in
/-- At every genuine thick-wire row index, the canonical header and the final
bank recorded by the selected level meet the native column's operand contract. -/
theorem ab_recorded (space : (plan).stop < 2 ^ w)
    (alloc : ShrinkABSliceTable.Layout (ShrinkInput.thickBank X T origin)
      (ShrinkInput.piecesBank X T origin) bundleCount count Q bankBase)
    (bankWords : IndexedStarts.Stored bank
      (ShrinkSliceArrays.thickWidths (P) X.shrinkOrder X.packingWidth ((P).bundle m))
      (ShrinkSliceArrays.abWidths (P) X.shrinkNumber X.packingWidth ((P).bundle m)) mem)
    (dir : Bool) (x : (P).PlacedHalf X.packingWidth side (ShrinkOldHalves.abSite X m dir))
    (i : Fin count) :
    let G := geometry X T origin space
    let nodes := fun u ↦ older + stride * PortRefresh.ArgumentAddress.siteOrdinal X u
    let row := ShrinkAB.Physical.row X m G.arcFit G.bucketFit i A nodes side dir x
      (first := bankBase) (dest := (heap).staging)
    row.Recorded ((O.cdHeader a).fields.setup d count Q dir i.val) pub state mem := by
  intro G nodes row
  have h := heads X F sel m O pub state level mem A T origin older stride bankBase
    hidden slotStride hist levelData live
  have countBound : count ≤ Q := by unfold pieceCount; omega
  exact ShrinkAB.Physical.recorded X (O.cdHeader a).fields pub state mem m h.ab G.arcFit
    G.bucketFit G.piecesFit i A side dir x T older stride h.child old.incidence G.degreeFit
    G.regions G.nrows (countBound.trans G.cap) old.preimages old.ranked alloc
    ⟨mem, bankWords, fun _ _ _ ↦ rfl⟩

/-- The descriptor's computed C operand points to the stored bit of the
selected old half-assignment. -/
theorem read_C (header : ShrinkCallFields.Stored pub state mem X m (O.inputs a) heap term dense 10
      side (cdBase X m A older stride)) {endAddr : ℕ} (priv : Word w → Word w)
    (x : (P).PlacedHalf X.packingWidth side ((P).placement side ((P).C m)))
    (prepared : ShrinkOldHalves.PlacedPackets X side A
      (fun u ↦ older + stride * PortRefresh.ArgumentAddress.siteOrdinal X u) priv _ x endAddr)
    (i : Fin (X.packingWidth m.1)) :
    priv (ev ((O.inputs a).cd false) + (i.val : Word w)) =
      PrivateFields.bitValue w ((P).localCWord X.packingWidth side m x i) := by
  rw [header.cd, ← Nat.cast_add]
  exact ShrinkOldHalves.read_C X side m prepared i

/-- The descriptor's D operand selects the opposite physical end, using its
independent child packet even when source and target coincide. -/
theorem read_D (header : ShrinkCallFields.Stored pub state mem X m (O.inputs a) heap term dense 10
      side (cdBase X m A older stride)) {endAddr : ℕ} (priv : Word w → Word w)
    (x : (P).PlacedHalf X.packingWidth side ((P).roleD side m))
    (prepared : ShrinkOldHalves.PlacedPackets X side A
      (fun u ↦ older + stride * PortRefresh.ArgumentAddress.siteOrdinal X u) priv _ x endAddr)
    (i : Fin (X.packingWidth m.1)) :
    priv (ev ((O.inputs a).cd true) + (i.val : Word w)) =
      PrivateFields.bitValue w ((P).localDWord X.packingWidth side m x i) := by
  rw [header.cd, ← Nat.cast_add]
  exact ShrinkOldHalves.read_D X side m prepared i

end PairSimulation.ShrinkCallHeader

end VPVNP
end Computability
end OAI

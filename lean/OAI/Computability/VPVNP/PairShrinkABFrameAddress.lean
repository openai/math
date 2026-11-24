import OAI.Computability.VPVNP.PairResidentFrameColumn
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace
import OAI.Computability.VPVNP.PairShrinkABNative
import OAI.Computability.VPVNP.PairShrinkOldHalfAddresses
import OAI.Computability.VPVNP.CompressorBundleRankedInput
import OAI.Computability.VPVNP.CompressorShrinkMotifOrder

/-!
# Physical pointers for the AB operand copies

The resident map supplies its dense motif ordinal. Dividing this by the
number of AB pieces selects a thick-wire list, in the order actually written
by the preimage scan. Its old arc ID locates the independent child half. The
rank at that same ID selects the source-major slice frame in the bundle bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkAB.Physical

open Compression Compression.PackingData CompressorRecords CompressorRecords.PhaseRecipe
open BurstRAM BurstRAM.PrivateRAM BundleLists ShrinkSliceArrays
open scoped Fin.CommRing

/-- Operands available at the entry of a resident AB copy. -/
structure Header where
  /-- Private argument-arena parameters and incidence heads for recovering an old endpoint's
  half-wire address. -/
  oldHalf : ShrinkOldHalves.Physical.Header
  /-- Dense ordinal of the selected CD motif. Division by the piece count gives its bundle
  number. -/
  motif : Expr
  /-- Start of the classified bundle rows containing original arc IDs in append order. -/
  lists : Expr
  /-- Distance in words between consecutive classified bundle rows. -/
  listStride : Expr
  /-- Head of the array mapping each old arc ID to its rank within its bundle. -/
  rankBase : Expr
  /-- Base of the consecutive AB frame banks, one bank per bundle. -/
  banks : Expr
  /-- Private staging address where this party gathers its AB demand word. -/
  destination : Expr

/-- Quotient of the dense motif ordinal by the fixed number of pieces in each bundle. -/
def Header.bundle (h : Header) (pieces : ℕ) := h.motif.div (.lit pieces)

/-- Remainder of the dense motif ordinal modulo the bundle's piece count, used to select the
frame column. -/
def Header.piece (h : Header) (pieces : ℕ) := h.motif.mod (.lit pieces)

/-- The row contains original old arc IDs in append order. -/
def Header.arc (h : Header) (pieces index : ℕ) : Expr :=
  .load ((h.lists.add ((h.bundle pieces).mul h.listStride)).add (.lit index))

/-- Address the three-word AB frame at the old arc's stored rank and the motif's piece number,
after the bundle's two width arrays. -/
def Header.frame (h : Header) (count pieces index : ℕ) : Expr :=
  let rank := Expr.load (h.rankBase.add (h.arc pieces index))
  let bank := h.banks.add ((h.bundle pieces).mul (.lit (IndexedStarts.capacity count pieces)))
  (bank.add (.lit (count + pieces))).add
    ((Expr.lit 3).mul ((rank.mul (.lit pieces)).add (h.piece pieces)))

variable {w a g : ℕ} (X : State a (packingLaneBits a g))
local notation "P" => X.packingData
local notation "d" => 2 ^ a
local notation "c" => Shrink.colors a
local notation "arcs" => BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "arcCount" => Fintype.card X.Base * 2 ^ (packingLaneBits a g) * d
local notation "bundleCount" => (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * d
local notation "count" => 2 ^ c * d / 4
local notation "pieces" => pieceCount d c

/-- Classical equality on old base vertices for the thick-arc fiber and its ordinal
enumeration. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Convert a fixed loop ordinal to the old thick arc encountered by the
original ID list. This is a bijection even if the key ordering differs. -/
noncomputable def members (arcFit : arcCount ≤ 2 ^ w)
    (bucketFit : bundleCount + bundleCount ≤ 2 ^ w)
    (b : Port X.Base (BitWord (Shrink.J a)) (BitWord g) d) :
    Fin count ≃ (P).ThickFiber b :=
  let size := arcList_length (P) arcs sites (State.two_le_packingColors a) arcFit bucketFit (.inl b)
  ((finCongr size.symm).trans (ordinalEquiv (P) arcs sites arcFit bucketFit (.inl b))).trans
    (thickEquiv (P) b)

variable (h : Header) (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
variable (q : Fin 6 → Word w) (s : Fin 5 → Word w) (first dest : ℕ)

/-- Agreement of the evaluated AB header with the selected motif ordinal, classified lists,
rank array, frame bank, and private destination. -/
structure Header.Stored (m : (P).Motif) : Prop where
  motif : (h.motif.eval pub state mem).val = (ShrinkMotifOrder.stateNumber X m).val
  lists : h.lists.eval pub state mem = q 5
  listStride : h.listStride.eval pub state mem = q 4
  rankBase : h.rankBase.eval pub state mem = s 1
  banks : h.banks.eval pub state mem = CursorRAM.encode w first
  destination : h.destination.eval pub state mem = CursorRAM.encode w dest

private theorem of_val {x : Word w} {n : ℕ} (h : x.val = n) : x = CursorRAM.encode w n := by
  subst n
  exact Fin.ext (Nat.mod_eq_of_lt x.isLt).symm

private theorem unpack {x y : Word w} {u v : ℕ} (eqn : x.val = u * y.val + v) (lo : v < y.val) :
    (BinaryOp.div.eval x y).val = u ∧ (BinaryOp.mod.eval x y).val = v := by
  have q : x.val / y.val = u := by
    rw [eqn, Nat.mul_comm u, Nat.mul_add_div (Nat.zero_lt_of_lt lo),
      Nat.div_eq_of_lt lo, Nat.add_zero]
  exact ⟨(Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)).trans q,
    (Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)).trans (eqn ▸ Nat.mul_add_mod_of_lt lo)⟩

variable {q s first dest}
variable (m : X.packingData.Motif) (stored : h.Stored X pub state mem q s first dest m)
variable (arcFit : Fintype.card X.Base * 2 ^ (packingLaneBits a g) * 2 ^ a ≤ 2 ^ w)
variable (bucketFit : (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a +
  (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a ≤ 2 ^ w)
variable (pieceFit : pieceCount (2 ^ a) (Shrink.colors a) < 2 ^ w)
local notation "b" => X.packingData.bundle m
local notation "port" => portIndex sites b
local notation "fiber" => Subtype.mk m (Eq.refl b)
local notation "piece" => X.shrinkNumber b fiber

include stored pieceFit in
theorem coordinates :
    (h.bundle pieces).eval pub state mem = CursorRAM.encode w (port).val ∧
      (h.piece pieces).eval pub state mem = CursorRAM.encode w (piece).val := by
  have dy : (CursorRAM.encode w pieces).val = pieces := Nat.mod_eq_of_lt pieceFit
  have hm := stored.motif.trans (ShrinkMotifOrder.number_val (P) X.shrinkNumber sites m)
  have v := unpack (x := h.motif.eval pub state mem) (y := CursorRAM.encode w pieces)
    (u := (port).val) (v := (piece).val) (by rw [dy]; exact hm)
    (by rw [dy]; exact (piece).isLt)
  exact ⟨of_val v.1, of_val v.2⟩

variable (i : Fin (2 ^ (Shrink.colors a) * 2 ^ a / 4))
local notation "t" => members X arcFit bucketFit b i

private theorem actual_id (e : BundleKeys.OldArc X.Base a g) :
    Fin.ofNat (2 ^ w) (arcs e).val =
      IncidenceDirectory.actualPort X (packingInputEdges X.Base a g e) := by
  rw [BundleKeys.oldArcOrder_val, Shrink.oldNumber_original]
  rfl

open private row_fits from OAI.Computability.VPVNP.CompressorRecordPreimageScan

include stored pieceFit in
theorem old_id (reg : RowRegions q) (nrows : (q 2).val = bundleCount + bundleCount)
    (cap : count ≤ (q 4).val) (filled : PreimagesAt q (wordOwner (P) arcs sites) mem arcCount) :
    (h.arc pieces i.val).eval pub state mem = IncidenceDirectory.actualPort X
      (packingInputEdges X.Base a g (t).1.1) := by
  let v : Word w := Fin.ofNat _ (bucketIndex sites (.inl b)).val
  have vw : v.val = (bucketIndex sites (.inl b)).val :=
    Nat.mod_eq_of_lt ((bucketIndex sites (.inl b)).isLt.trans_le bucketFit)
  have below : v < q 2 := by
    change v.val < (q 2).val
    rw [vw, nrows]
    exact (bucketIndex sites (.inl b)).isLt
  have vport : CursorRAM.encode w (port).val = v := rfl
  have coord := (coordinates X h pub state mem m stored pieceFit).1.trans vport
  change mem ((h.lists.eval pub state mem + (h.bundle pieces).eval pub state mem *
    h.listStride.eval pub state mem) + (i.val : Word w)).val = _
  rw [stored.lists, stored.listStride, coord]
  change mem ((rowAt q v) + (i.val : Word w)).val = _
  have endRow := row_fits reg below
  have valid : (rowAt q v).val + i.val < 2 ^ w := by have := i.isLt; omega
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt valid]
  have size := arcList_length (P) arcs sites (State.two_le_packingColors a)
    arcFit bucketFit (.inl b)
  let j := Fin.cast size.symm i
  have read := (filled.rows v below).2 j
  have he := ordinalEquiv_id (P) arcs sites arcFit bucketFit (.inl b) j
  exact read.trans (he.trans (actual_id X (t).1.1))

include stored pieceFit in
theorem old_rank (reg : RowRegions q) (nrows : (q 2).val = bundleCount + bundleCount)
    (cap : count ≤ (q 4).val) (filled : PreimagesAt q (wordOwner (P) arcs sites) mem arcCount)
    (ranked : BundleWidthScatter.RankedInput (P) X.shrinkNumber X.shrinkOrder arcs sites s mem
      X.packingWidth) :
    (Expr.load (h.rankBase.add (h.arc pieces i.val))).eval pub state mem =
      CursorRAM.encode w (X.shrinkOrder b (t)).val := by
  have arc := old_id X h pub state mem m stored arcFit bucketFit pieceFit i reg nrows cap filled
  change mem (h.rankBase.eval pub state mem + (h.arc pieces i.val).eval pub state mem).val = _
  rw [stored.rankBase, arc, ← actual_id]
  have rank := ranked.ranks (t).1.1
  rw [BundleWidthScatter.rank_thick (P) X.shrinkNumber X.shrinkOrder (t)] at rank
  exact rank


variable {thick ab : Fin 5 → Word w}

private theorem enc_add (x y : ℕ) : CursorRAM.encode w x + CursorRAM.encode w y =
    CursorRAM.encode w (x + y) := Fin.ext (Nat.add_mod x y _).symm

private theorem enc_mul (x y : ℕ) : CursorRAM.encode w x * CursorRAM.encode w y =
    CursorRAM.encode w (x * y) := Fin.ext (Nat.mul_mod x y _).symm

local notation "bank" => ShrinkABSliceTable.bank (w := w) first count pieces (Fin.val port)

include stored pieceFit in
theorem frame_address (reg : RowRegions q) (nrows : (q 2).val = bundleCount + bundleCount)
    (cap : count ≤ (q 4).val) (filled : PreimagesAt q (wordOwner (P) arcs sites) mem arcCount)
    (ranked : BundleWidthScatter.RankedInput (P) X.shrinkNumber X.shrinkOrder arcs sites s mem
      X.packingWidth)
    (alloc : ShrinkABSliceTable.Layout thick ab bundleCount count pieces first) :
    (h.frame count pieces i.val).eval pub state mem =
      CursorRAM.encode w (ShrinkAB.frame (P) X.shrinkNumber X.shrinkOrder fiber bank (t)) := by
  obtain ⟨bundle, part⟩ := coordinates X h pub state mem m stored pieceFit
  have r := old_rank X h pub state mem m stored arcFit bucketFit pieceFit i
    reg nrows cap filled ranked
  change (h.banks.eval pub state mem + (h.bundle pieces).eval pub state mem *
    CursorRAM.encode w (IndexedStarts.capacity count pieces) +
      CursorRAM.encode w (count + pieces)) +
    CursorRAM.encode w 3 * ((Expr.load (h.rankBase.add (h.arc pieces i.val))).eval pub state mem *
      CursorRAM.encode w pieces + (h.piece pieces).eval pub state mem) = _
  rw [stored.banks, bundle, part, r]
  simp only [enc_mul, enc_add, ShrinkAB.frame, ShrinkABSliceTable.bank_val alloc, Nat.add_assoc]


/-- The static pointer program for one frame in the thick-wire row. -/
def Header.setup (H : Header) (degree oldCount pieceCount : ℕ) (dir : Bool) (idx : ℕ) :
    ResidentColumn.Setup :=
  ⟨H.oldHalf.field degree (H.arc pieceCount idx) dir, H.destination,
    H.frame oldCount pieceCount idx, false⟩

variable (arena : NodeArguments.Arena) (nodes : X.network.Site → ℕ) (layout dir : Bool)
local notation "abSite" => ShrinkOldHalves.abSite X m dir
variable (x : X.packingData.PlacedHalf X.packingWidth layout (ShrinkOldHalves.abSite X m dir))
local notation "data" => ShrinkOldHalves.abData X layout m dir x
local notation "slice" =>
  X.packingData.demandSlice X.shrinkNumber X.shrinkOrder X.packingWidth b t fiber

/-- Logical copy at the actual old-ID row index. Its source and target offsets
refer to the same thick-rank / motif-rank frame as the pointer calculation. -/
noncomputable def row : ResidentColumn.Row :=
  ⟨ShrinkOldHalves.address X arena nodes (t).1.1 dir, dest,
    ShrinkAB.frame (P) X.shrinkNumber X.shrinkOrder fiber bank (t),
    (slice).sourceOffset, (slice).targetOffset,
    ShrinkAB.copyBits (P) X.shrinkNumber X.shrinkOrder X.packingWidth fiber data (t)⟩

open private frame_fit from OAI.Computability.VPVNP.PairShrinkABNative

set_option maxHeartbeats 1200000 in
-- Reconcile the concrete state numbering with both dependent bank arrays.
include stored pieceFit in
theorem recorded (T : IncidenceDirectory w) (older stride : ℕ)
    (hs : h.oldHalf.Stored T arena older stride pub state mem)
    (cols : T.ActualColumns X mem) (degreeFits : d < 2 ^ w)
    (reg : RowRegions q) (nrows : (q 2).val = bundleCount + bundleCount)
    (cap : count ≤ (q 4).val) (filled : PreimagesAt q (wordOwner (P) arcs sites) mem arcCount)
    (ranked : BundleWidthScatter.RankedInput (P) X.shrinkNumber X.shrinkOrder arcs sites s mem
      X.packingWidth)
    (alloc : ShrinkABSliceTable.Layout thick ab bundleCount count pieces first)
    (image : ShrinkABSliceTable.Image bank (thickWidths (P) X.shrinkOrder X.packingWidth b)
      (abWidths (P) X.shrinkNumber X.packingWidth b) mem) :
    let ptr := fun u ↦ older + stride * PortRefresh.ArgumentAddress.siteOrdinal X u
    (row X m arcFit bucketFit i arena ptr layout dir x (first := first) (dest := dest)).Recorded
      (h.setup d count pieces dir i.val) pub state mem := by
  intro ptr
  have aid := old_id X h pub state mem m stored arcFit bucketFit pieceFit i reg nrows cap filled
  have word := ShrinkOldHalves.Physical.field_eq X h.oldHalf T arena older stride pub state mem
    hs cols arcFit degreeFits (t).1.1 (h.arc pieces i.val) aid dir
  have sp := ShrinkABSliceTable.space alloc port
  have oldSize : (thickWidths (P) X.shrinkOrder X.packingWidth b).length = count := List.length_ofFn
  have newSize : (abWidths (P) X.shrinkNumber X.packingWidth b).length = pieces := List.length_ofFn
  have sd := image.stored (input := ShrinkABSliceTable.columns thick ab (port).val)
    (by rw [oldSize, newSize]; exact sp)
  have words := frame_words (P) X.shrinkNumber X.shrinkOrder X.packingWidth fiber sd (t)
  have len : (ShrinkAB.copyBits (P) X.shrinkNumber X.shrinkOrder X.packingWidth
      fiber data (t)).length =
      (slice).length := List.length_ofFn
  exact ⟨word, stored.destination, frame_address X h pub state mem m stored arcFit bucketFit
    pieceFit i reg nrows cap filled ranked alloc,
    frame_fit (P) X.shrinkNumber X.shrinkOrder fiber bank (t) sp.fits,
    words.1.trans len.symm, fun pos ↦ words.2 (len ▸ pos)⟩

set_option maxHeartbeats 800000 in
-- Reduce the typed slice coordinate through the numbered old arc and field widths.
theorem reads {endAddr : ℕ} (priv : Word w → Word w)
    (ready : ShrinkOldHalves.PlacedPackets X layout arena nodes priv abSite x endAddr) :
    (row X m arcFit bucketFit i arena nodes layout dir x (first := first) (dest := dest)).reads
      priv := by
  intro j
  have len : (row X m arcFit bucketFit i arena nodes layout dir x
      (first := first) (dest := dest)).bits.length = (slice).length := List.length_ofFn
  let k : Fin (slice).length := ⟨j.val, len ▸ j.isLt⟩
  have bit := ShrinkOldHalves.read_ab X layout m dir ready (t)
    ⟨(slice).sourceOffset + j.val,
      ShrinkAB.source_bound (P) X.shrinkNumber X.shrinkOrder X.packingWidth fiber (t) k⟩
  simpa only [row, ShrinkAB.copyBits, List.getElem_ofFn, Nat.add_assoc] using bit

theorem fits (pivot : ℕ) (old : ∀ u, arena.base (nodes u) + arena.stride ≤ pivot)
    (start : pivot ≤ dest) (room : dest + (P).abWidth X.shrinkNumber X.packingWidth m < 2 ^ w)
    {endAddr : ℕ} {priv : Word w → Word w}
    (ready : ShrinkOldHalves.PlacedPackets X layout arena nodes priv abSite x endAddr) :
    (row X m arcFit bucketFit i arena nodes layout dir x (first := first) (dest := dest)).Fits w
      pivot := by
  let e := (t).1.1
  let u := ShrinkOldHalves.position X e dir
  have placed : abSite = (P).placement layout u := by
    cases dir with
    | false =>
      exact (congrArg Prod.fst (t).2.symm).trans ((P).place_thick_source layout (t).1).symm
    | true =>
      exact (congrArg (fun z ↦ ((P).siteGraph.target z).1) (t).2.symm).trans
        ((P).place_thick_target layout (t).1).symm
  let z := (X.packingHalfEquiv u).symm (x u placed)
  let v := X.packingInputIso.site u
  let j := ShrinkOldHalves.slot X e dir
  have endField := NodeArguments.field_end_le X v z arena (nodes v) dir j
  have width : X.halfWidth v dir j = X.packingWidth e := by
    simpa only [List.length_ofFn] using congrArg List.length (ShrinkOldHalves.slot_bits X e dir z)
  have frameWidth : (NodeArguments.packed X v z).length ≤ arena.stride := (ready u placed).1.2.1
  have ends := old v
  rw [width] at endField
  let r := row X m arcFit bucketFit i arena nodes layout dir x (first := first) (dest := dest)
  have len : r.bits.length = (slice).length := List.length_ofFn
  constructor
  · intro pos
    have last : (slice).length - 1 < (slice).length := by
      change 0 < r.bits.length at pos
      omega
    have edge := ShrinkAB.source_bound (P) X.shrinkNumber X.shrinkOrder X.packingWidth fiber
      (t) ⟨_, last⟩
    change (slice).sourceOffset + ((slice).length - 1) < X.packingWidth e at edge
    change arena.fieldAddress X v (nodes v) dir j + (slice).sourceOffset + r.bits.length ≤ pivot
    omega
  · exact start
  · intro pos
    change 0 < r.bits.length at pos
    have bound := ShrinkAB.target_bound (P) X.shrinkNumber X.shrinkOrder X.packingWidth fiber
      (t) (len ▸ pos)
    change (slice).targetOffset + (slice).length ≤
      (P).abWidth X.shrinkNumber X.packingWidth m at bound
    change dest + (slice).targetOffset + r.bits.length < 2 ^ w
    omega


set_option maxHeartbeats 1200000 in
-- The physical and logical folds carry different dependent presentations of each wire.
/-- The final native column writes every coordinate of the selected resident
AB operand, although the original append order may differ from thick rank. -/
theorem writes_operand (priv : Word w → Word w)
    (room : dest + (P).abWidth X.shrinkNumber X.packingWidth m ≤ 2 ^ w)
    (j : Fin ((P).abWidth X.shrinkNumber X.packingWidth m)) :
    let rs := fun i ↦ row X m arcFit bucketFit i arena nodes layout dir x
      (first := first) (dest := dest)
    ResidentColumn.writes rs (List.finRange count) priv ((dest + j.val : ℕ) : Word w) =
      PrivateFields.bitValue w (ShrinkAB.operand (P) X.shrinkNumber X.shrinkOrder
        X.packingWidth fiber (State.two_le_packingColors a) (Nat.two_pow_pos a) data j) := by
  intro rs
  let o := members X arcFit bucketFit b
  have all (z : (P).ThickFiber b) : z ∈ (List.finRange count).map o := by
    exact List.mem_map.mpr ⟨o.symm z, List.mem_finRange _, o.apply_symm_apply z⟩
  have fill := ShrinkAB.fill_operand (P) X.shrinkNumber X.shrinkOrder X.packingWidth fiber
    (State.two_le_packingColors a) (Nat.two_pow_pos a) dest room data
    ((List.finRange count).map o) priv j (Or.inl (all _))
  rw [ShrinkAB.fill, List.foldl_map] at fill
  exact fill

end PairSimulation.ShrinkAB.Physical

end VPVNP
end Computability
end OAI

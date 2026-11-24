import OAI.Computability.VPVNP.PairShrinkABFrameAddress
import OAI.Computability.VPVNP.CompressorFormulaFootprint
import OAI.Computability.VPVNP.PairShrinkArgumentReadBounds
import OAI.Computability.VPVNP.PairShrinkCallABI

/-!
# External reads of a shrinking AB copy

The copy visits the old-port list in append order, resolves the selected
arc's thick rank, and follows the frame at that rank. Its source payload
lives in a private child packet. Only the published old level, incidence
columns, append list, rank column and slice bank are read externally.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkAB.Physical

open Compression Compression.PackingData CompressorRecords CompressorRecords.PhaseRecipe
open BurstRAM BundleLists
open scoped Fin.CommRing

variable {w : ℕ}

private theorem add_le (x y : Word w) : (x + y).val ≤ x.val + y.val := Nat.mod_le ..

private theorem mul_le (x y : Word w) : (x * y).val ≤ x.val * y.val := Nat.mod_le ..

/-- Access the identifier at the chosen position of the thick row. -/
theorem Header.arc_reads (hdr : Header) (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
    (H pieces bucket buckets idx cap : ℕ) (list : Word w)
    (readsMotif : hdr.motif.ReadsFrom (· < H) pub state mem)
    (readsList : hdr.lists.ReadsFrom (· < H) pub state mem)
    (readsStride : hdr.listStride.ReadsFrom (· < H) pub state mem)
    (listEq : hdr.lists.eval pub state mem = list)
    (strideEq : (hdr.listStride.eval pub state mem).val = cap)
    (coord : (hdr.bundle pieces).eval pub state mem = (bucket : Word w))
    (inBucket : bucket < buckets) (inSlot : idx < cap)
    (room : list.val + buckets * cap ≤ H) :
    (hdr.arc pieces idx).ReadsFrom (· < H) pub state mem := by
  refine ⟨⟨⟨readsList, ⟨⟨readsMotif, trivial⟩, readsStride⟩⟩, trivial⟩, ?_⟩
  change ((hdr.lists.eval pub state mem + (hdr.bundle pieces).eval pub state mem *
    hdr.listStride.eval pub state mem) + (idx : Word w)).val < H
  rw [listEq, coord]
  let width := hdr.listStride.eval pub state mem
  change ((list + (bucket : Word w) * width) + (idx : Word w)).val < H
  have pos : ((bucket : Word w) * width).val ≤ bucket * cap :=
    (mul_le _ _).trans (strideEq ▸ Nat.mul_le_mul_right width.val (Nat.mod_le ..))
  have bound := Nat.mul_le_mul_right cap inBucket
  rw [Nat.succ_mul] at bound
  have cell := add_le (list + (bucket : Word w) * width) (idx : Word w)
  have row := add_le list ((bucket : Word w) * width)
  have offset : (idx : Word w).val ≤ idx := Nat.mod_le ..
  omega

/-- The only additional indirect read in the frame expression is the rank
at the actual outgoing ID obtained from the old list. -/
theorem Header.frame_reads (hdr : Header) (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
    (H count pieces idx slots : ℕ)
    (motif : hdr.motif.ReadsFrom (· < H) pub state mem)
    (banks : hdr.banks.ReadsFrom (· < H) pub state mem)
    (rank : hdr.rankBase.ReadsFrom (· < H) pub state mem)
    (arc : (hdr.arc pieces idx).ReadsFrom (· < H) pub state mem)
    (arcBound : ((hdr.arc pieces idx).eval pub state mem).val < slots)
    (room : (hdr.rankBase.eval pub state mem).val + slots ≤ H) :
    (hdr.frame count pieces idx).ReadsFrom (· < H) pub state mem := by
  have rankRead : (Expr.load (hdr.rankBase.add (hdr.arc pieces idx))).ReadsFrom
      (· < H) pub state mem :=
    ⟨⟨rank, arc⟩, (add_le _ _).trans_lt ((Nat.add_lt_add_left arcBound _).trans_le room)⟩
  exact ⟨⟨⟨banks, ⟨⟨motif, trivial⟩, trivial⟩⟩, trivial⟩,
    ⟨trivial, ⟨⟨rankRead, trivial⟩, ⟨motif, trivial⟩⟩⟩⟩

variable {V G Tag L : Type} {d c : ℕ}
variable [AddCommGroup G] [AddCommGroup Tag] [AddCommGroup L]

/-- All three external reads of an indexed frame lie within its own AB bank. -/
theorem frame_lt_end (P : PackingData V G Tag L d c)
    (number : P.BundleNumbering) (order : P.ThickNumbering)
    {b : Site V Tag L × Fin d} (m : P.MotifFiber b) (B : Word w) (a : P.ThickFiber b)
    (j : Fin 3) :
    ShrinkAB.frame P number order m B a + j.val <
      B.val + IndexedStarts.capacity (2 ^ c * d / 4) (pieceCount d c) := by
  have h : (order b a).val * pieceCount d c + (number b m).val <
      (2 ^ c * d / 4) * pieceCount d c :=
    (Nat.add_lt_add_left (number b m).isLt _).trans_le
      ((Nat.succ_mul _ _).symm ▸ Nat.mul_le_mul_right _ (order b a).isLt)
  have hj := j.isLt
  unfold ShrinkAB.frame IndexedStarts.capacity
  omega

end PairSimulation.ShrinkAB.Physical

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.PackingData CompressorRecords CompressorRecords.PhaseRecipe
open Compression.ShrinkMotif MotifGrid MotifBlocks MotifConversion
open ShrinkPartyColumns ShrinkOldHalves.Physical CompressorRecords.ShrinkSlots
open scoped Fin.CommRing

variable {w a b g : ℕ} {K : Type*} [_root_.Field K] {δ factor : ℝ}
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
variable {m : X.packingData.Motif} {party : Fin 6}
variable (J : Job X F ready sel m party w)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "count" => 2 ^ (Shrink.colors a) * 2 ^ a / 4
local notation "pieces" => pieceCount (2 ^ a) (Shrink.colors a)
local notation "arcs" => Fintype.card X.Base * 2 ^ packingLaneBits a g * 2 ^ a
local notation "buckets" => (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a
local notation "bundle" => X.packingData.bundle m
local notation "siteOrd" => Shrink.packedIndex (a := a) (g := g) X.baseIndex
local notation "port" => BundleLists.portIndex siteOrd bundle
local notation "side" => selectedLayout X F sel

/-- External extents of the selected old-level data used by a native AB copy. -/
structure Job.ABAreas (level : Word w) (T : IncidenceDirectory w) (origin H : ℕ) : Prop where
  levelEnd : level.val + 60 ≤ H
  classifier : (ShrinkInput.plan X origin).stop ≤ H
  outgoing : T.actualOut.val + arcs ≤ H
  incoming : T.actualIn.val + arcs ≤ H
  widths : T.width.val + arcs ≤ H
  intersections : J.first + buckets * IndexedStarts.capacity count pieces ≤ H

variable {pub : Fin 5 → Word w} {state level : Word w} {mem : Memory w} {T : IncidenceDirectory w}
variable {origin H : ℕ}

/-- The enclosing shrink role provides these entry expressions. Its concrete
register ABI only reads the old level's degree-independent length word. -/
structure InputsReadable (O : ShrinkCallHeader.Operands) (H : ℕ) (pub : Fin 5 → Word w)
    (state : Word w) (mem : Memory w) : Prop where
  level : O.level.ReadsFrom (· < H) pub state mem
  motif : O.motif.ReadsFrom (· < H) pub state mem
  arguments : O.arguments.ReadsFrom (· < H) pub state mem
  stride : O.argumentStride.ReadsFrom (· < H) pub state mem
  hidden : O.hidden.ReadsFrom (· < H) pub state mem
  slot : O.slotStride.ReadsFrom (· < H) pub state mem

private theorem cell_reads {O : ShrinkCallHeader.Operands}
    (entry : O.level.eval pub state mem = level) (read : O.level.ReadsFrom (· < H) pub state mem)
    (room : level.val + 60 ≤ H) (i : ℕ) (hi : i < 60) :
    (ShrinkCD.Published.load O.level i).ReadsFrom (· < H) pub state mem := by
  refine ⟨⟨read, trivial⟩, ?_⟩
  change (O.level.eval pub state mem + (i : Word w)).val < H
  rw [entry, Fin.val_add]
  exact (Nat.mod_le ..).trans_lt
    ((Nat.add_lt_add_left ((Nat.mod_le ..).trans_lt hi) _).trans_le room)

/-- A caller may supply any bounded old outgoing-ID expression, including
the CD rank-selection expression or one cell of the thick AB list. -/
theorem Job.old_field_reads (O : ShrinkCallHeader.Operands)
    (old : J.OldPublished O pub state mem level T origin)
    (ins : InputsReadable O H pub state mem) (areas : J.ABAreas level T origin H)
    (e : BundleKeys.OldArc X.Base a g) (arc : Expr) (dir : Bool)
    (arcEq : arc.eval pub state mem =
      IncidenceDirectory.actualPort X (packingInputEdges X.Base a g e))
    (arcRead : arc.ReadsFrom (· < H) pub state mem) :
    ((O.cdHeader a).fields.oldHalf.field (2 ^ a) arc dir).ReadsFrom (· < H) pub state mem := by
  let hdr := (O.cdHeader a).fields.oldHalf
  have heads := ShrinkCallHeader.heads X F sel m O pub state level mem J.arena T origin
    J.older J.pitch J.first J.scratch.hidden J.scratch.stride J.scratch.hist old.levelData old.live
  have geometry := ShrinkCallHeader.geometry X T origin old.space
  have read := cell_reads old.live.header ins.level areas.levelEnd
  let u := X.packingInputIso.site (ShrinkOldHalves.position X e dir)
  let j := ShrinkOldHalves.slot X e dir
  have oriented := ShrinkOldHalves.Physical.port_eq X hdr T J.arena J.older J.pitch pub state mem
    heads.child old.tables.incidence e arc arcEq dir
  exact ArgumentReadBounds.old_field X u j hdr T J.arena heads.child old.tables.incidence
    J.arcFit geometry.degreeFit arc (packingInputEdges X.Base a g e) dir arcEq oriented H
    ⟨ins.arguments, ins.stride, read 58 (by decide), read 59 (by decide)⟩ arcRead
    (read 57 (by decide)) (read 14 (by decide)) (read 15 (by decide))
    areas.outgoing areas.incoming areas.widths

/-- External bounds for all six pointer-program operands and all three
direct frame reads at a genuine thick-wire visit of an active AB party. -/
theorem Job.ab_readBounds (O : ShrinkCallHeader.Operands) (nodeExpr : Expr)
    (old : J.OldPublished O pub state mem level T origin)
    (ins : InputsReadable O H pub state mem) (areas : J.ABAreas level T origin H)
    (hc : none ∈ columns party side) (i : Fin count) :
    let c : At party side := ⟨none, hc⟩
    (∀ f : Fin 6, ((setups O nodeExpr a b party side c i).operands f).ReadsFrom
      (· < H) pub state mem) ∧ ∀ k : Fin 3, (J.row c i).frame + k.val < H := by
  intro c
  let hdr := (O.cdHeader a).fields
  let Z := ShrinkInput.plan X origin
  let q := Z.collectBank w
  let t := ShrinkAB.Physical.members X J.arcFit J.bucketFit bundle i
  let e := t.1.1
  let dir := decide (party = 1)
  have heads := ShrinkCallHeader.heads X F sel m O pub state level mem J.arena T origin
    J.older J.pitch J.first J.scratch.hidden J.scratch.stride J.scratch.hist old.levelData old.live
  have G := ShrinkCallHeader.geometry X T origin old.space
  have countBound : count ≤ pieces := by unfold pieceCount; omega
  have idxBound := i.isLt.trans_le (countBound.trans G.cap)
  have coord := (ShrinkAB.Physical.coordinates X hdr pub state mem m heads.ab G.piecesFit).1
  have aid := ShrinkAB.Physical.old_id X hdr pub state mem m heads.ab J.arcFit J.bucketFit
    G.piecesFit i G.regions G.nrows (countBound.trans G.cap) old.tables.preimages
  have v := Z.values T (ShrinkInput.placementBank X T origin) Fintype.card_pos old.space
  have cells := cell_reads old.live.header ins.level areas.levelEnd
  have listRoom : (q 5).val + buckets * (q 4).val ≤ H := by
    rw [v.ids, v.stride]
    have half : buckets * Z.Q ≤ (2 * buckets) * Z.Q := Nat.mul_le_mul_right _ (by omega)
    have last : Z.ids + (2 * buckets) * Z.Q ≤ Z.stop := by
      change Z.gathered ≤ Z.gathered + Z.rectangleSize + Z.A
      omega
    exact ((Nat.add_le_add_left half _).trans last).trans areas.classifier
  have arcRead := hdr.arc_reads pub state mem H pieces (port).val buckets i.val (q 4).val (q 5)
    ins.motif (cells 46 (by decide)) trivial heads.ab.lists
    (congrArg Fin.val heads.ab.listStride) coord (port).isLt idxBound listRoom
  have arcBound : ((hdr.arc pieces i.val).eval pub state mem).val < arcs := by
    rw [aid, IncidenceDirectory.actualPort_number]
    exact (Nat.mod_le ..).trans_lt (IncidenceDirectory.actualOrder X _).isLt
  have rankRoom : (hdr.rankBase.eval pub state mem).val + arcs ≤ H := by
    rw [heads.ab.rankBase]
    change (Fin.ofNat (2 ^ w) Z.ranks).val + arcs ≤ H
    rw [v.ranks]
    exact areas.classifier
  have frameRead := hdr.frame_reads pub state mem H count pieces i.val arcs ins.motif
    (cells 43 (by decide)) (cells 45 (by decide)) arcRead arcBound rankRoom
  have sourceRead := J.old_field_reads O old ins areas e (hdr.arc pieces i.val) dir aid arcRead
  have destRead : (O.staging a).ReadsFrom (· < H) pub state mem :=
    ⟨ins.hidden, ⟨⟨trivial, ⟨⟨⟨cells 0 (by decide), ⟨trivial, cells 3 (by decide)⟩⟩, trivial⟩,
      trivial⟩⟩, ins.slot⟩⟩
  constructor
  · intro f
    fin_cases f <;> first | exact sourceRead | exact destRead | exact frameRead | trivial
  · intro k
    let B := ShrinkABSliceTable.bank (w := w) J.first count pieces (port).val
    have lower := ShrinkAB.Physical.frame_lt_end X.packingData X.shrinkNumber X.shrinkOrder
      (b := bundle) ⟨m, rfl⟩ B t k
    have bank : B.val = J.first + (port).val * IndexedStarts.capacity count pieces :=
      ShrinkABSliceTable.bank_val old.allocation port
    have rowBound := Nat.mul_le_mul_right (IndexedStarts.capacity count pieces) (port).isLt
    rw [Nat.succ_mul] at rowBound
    change (ShrinkAB.frame X.packingData X.shrinkNumber X.shrinkOrder ⟨m, rfl⟩ B t) + k.val < H
    exact lower.trans_le (by rw [bank, Nat.add_assoc]
                             exact (Nat.add_le_add_left rowBound _).trans areas.intersections)

/-- The canonical six-register ABI satisfies the expression bounds from the
published level header alone. Its only external operand load is cell 17. -/
theorem Job.abi_inputs_readable (degree : ℕ)
    (old : J.OldPublished (ShrinkCallABI.operands degree) pub state mem level T origin)
    (areas : J.ABAreas level T origin H) :
    InputsReadable (ShrinkCallABI.operands degree) H pub state mem := by
  have lengthRead := cell_reads old.live.header (show
    (ShrinkCallABI.operands degree).level.ReadsFrom (· < H) pub state mem from trivial)
    areas.levelEnd 17 (by decide)
  exact ⟨trivial, trivial, lengthRead, ⟨⟨trivial, lengthRead⟩, trivial⟩, trivial,
    ⟨lengthRead, lengthRead⟩⟩

/-- Bound every AB setup and frame load for the register ABI installed in
the shrinking party evaluator. -/
theorem Job.abi_ab_readBounds (degree : ℕ)
    (old : J.OldPublished (ShrinkCallABI.operands degree) pub state mem level T origin)
    (areas : J.ABAreas level T origin H) (hc : none ∈ columns party side) (i : Fin count) :
    let c : At party side := ⟨none, hc⟩
    let S := setups (ShrinkCallABI.operands degree) ShrinkCallABI.node a b party side c i
    (∀ f : Fin 6, (S.operands f).ReadsFrom (· < H) pub state mem) ∧
      ∀ k : Fin 3, (J.row c i).frame + k.val < H :=
  J.ab_readBounds (ShrinkCallABI.operands degree) ShrinkCallABI.node old
    (J.abi_inputs_readable degree old areas) areas hc i

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI

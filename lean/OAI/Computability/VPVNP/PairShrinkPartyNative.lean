import OAI.Computability.VPVNP.PairSimulationDFSHooks
import OAI.Computability.VPVNP.PairShrinkPartyColumns
import OAI.Computability.VPVNP.PairShrinkCallHeader
import OAI.Computability.VPVNP.PairShrinkCallDemandCells
import OAI.Computability.VPVNP.PairShrinkCallSupplyCells
import OAI.Computability.VPVNP.PairShrinkSurvivingSelected

/-!
# Executing the selected resident shrinking-party columns

The packed old assignments determine each AB source bit, and one stored
parent packet supplies every incident surviving column. The selected row
allocation and ordered-slot table determine the pointer computations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.State Compression.PackingData
open Compression.ShrinkMotif Compression.ShrinkEnergy MotifBlocks MotifGrid MotifConversion
open CompressorRecords CompressorRecords.ShrinkSlots CompressorRecords.ShrinkSliceSweep
open CompressorRecords.PortRefresh.ArgumentAddress NodeArguments ShrinkPartyColumns
open scoped Fin.CommRing

variable {a b g w : ℕ} {δ factor : ℝ} {K : Type*} [_root_.Field K]
variable (X : State a (packingLaneBits a g))
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (sel : X.ShrinkSelection F)
variable (m : X.packingData.Motif) (party : Fin 6)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X F sel
local notation "sub" => SlotLevel.Shape.subdivisions (levelShape (b := b) X)
local notation "slots" => X.shrinkStateIndex ready side
local notation "outState" => X.shrinkNext F ready sel
local notation "width" => branchWidth X F sel
local notation "atSite" => X.packingData.shrinkPartySite side m party
local notation "count" => 2 ^ (Shrink.colors a) * 2 ^ a / 4
local notation "pieces" => pieceCount (2 ^ a) (Shrink.colors a)
local notation "abWidth" => X.packingData.abWidth X.shrinkNumber X.packingWidth m
local notation "idx" => ShrinkMotifOrder.stateNumber X m
local notation "buckets" => (Fintype.card X.Base * (2 ^ (Shrink.J a) * 2 ^ g)) * 2 ^ a

/-- The current map job uses the selected branch and the same arena for its old
child packets and its new half-wire packet. The three slice bases are public. -/
structure Job (w : ℕ) where
  /-- Placed old half-wire assignments at the resident party site, used to recover the demand
  operands. -/
  old : ShrinkCallDemandCells.Old X side m party
  /-- The selected output site's independent half-wire assignment supplying the subdivided
  surviving fields in its packet. -/
  parent : (outState).network.Half atSite
  /-- Private argument arena shared by this parent packet and the old child packets. -/
  arena : Arena
  /-- Absolute DFS row address indexing the parent argument packet. -/
  node : ℕ
  /-- Private shared-field, staging, directory, and histogram addresses of this party's shrink
  map. -/
  scratch : ShrinkCallFields.Scratch
  /-- Start of the input layer's DFS rows, from which the old-site node addresses are computed. -/
  older : ℕ
  /-- Number of words per old DFS site row. -/
  pitch : ℕ
  /-- Start of the external AB frame-bank rectangle, with one indexed bank per bundle. -/
  first : ℕ
  /-- External base word for the selected shrinking term records. -/
  term : Word w
  /-- Word stride between successive dense motif term records. -/
  stride : ℕ
  /-- External base address of the surviving slice-width arrays in the selected allocation. -/
  widthBase : ℕ
  arcFit : Fintype.card X.Base * 2 ^ packingLaneBits a g * 2 ^ a ≤ 2 ^ w
  bucketFit : buckets + buckets ≤ 2 ^ w

variable {X F ready sel m party} (J : Job X F ready sel m party w)

/-- Locate an old site's child row using its site ordinal and the old layer's base and pitch. -/
noncomputable def Job.nodes (u : X.network.Site) := J.older + J.pitch * siteOrdinal X u

private theorem ab_hit (h : none ∈ columns party side) : party = if party = 1 then 1 else 0 := by
  have hs := (mem_columns party side none).mp h
  simp only [active, decide_eq_true_eq] at hs
  rcases hs with rfl | rfl <;> decide

private theorem supply_hit (dir : Bool) (t : Fin 4) (h : some (dir, t) ∈ columns party side) :
    party = ShrinkSurvivingOperands.party side t dir := by
  have hs := (mem_columns party side _).mp h
  change decide (party = ShrinkCallFields.supplyParty dir (side, t)) = true at hs
  cases dir <;> exact of_decide_eq_true hs

/-- At A or B, extract the placed old half-wire assignment used by the indicated end of the AB
demand. -/
noncomputable def Job.abHalf (dir : Bool) (hit : party = if dir then 1 else 0) :=
  ShrinkCallDemandCells.abHalf X side m dir (hit ▸ J.old)

private def movedHalf {N : NetworkKernel.Network} {u v : N.Site} (h : u = v) (z : N.Half u) :
    N.Half v := ⟨fun e he ↦ z.1 e (h.trans he), fun e he ↦ z.2 e (h.trans he)⟩

/-- Transport the resident parent's half-wire assignment to the equal site at the chosen end of
a surviving supply wire. -/
noncomputable def Job.half (dir : Bool) (t : Fin 4)
    (hit : party = ShrinkSurvivingOperands.party side t dir) :=
  movedHalf ((congrArg (X.packingData.shrinkPartySite side m) hit).trans
    (ShrinkSurvivingOperands.party_site X side m t dir)) J.parent

private theorem moved_packed {u v : (outState).network.Site} (e : u = v)
    (z : (outState).network.Half u) :
    packed (outState) v (movedHalf e z) = packed (outState) u z := by
  cases e
  rfl

theorem Job.packed_half (dir : Bool) (t : Fin 4)
    (hit : party = ShrinkSurvivingOperands.party side t dir) :
    packed (outState) _ (J.half dir t hit) = packed (outState) _ J.parent := moved_packed _ _

/-- The selected slice allocation determined by the term records, width base, and subdivision
profile for this shrink. -/
noncomputable def Job.allocation := selectedAllocation F X sel J.term J.stride J.widthBase sub

/-- Copy row for one old AB arc, with its child packet as source and the party's AB staging
word as destination. -/
noncomputable def Job.abRow (dir : Bool) (hit : party = if dir then 1 else 0) (i : Fin count) :=
  ShrinkAB.Physical.row X m J.arcFit J.bucketFit i J.arena J.nodes side dir (J.abHalf dir hit)
    (first := J.first) (dest := J.scratch.staging)

/-- Reverse-copy row for one subdivision of an incident surviving supply field, read from the
parent packet and placed in its unsplit staging word. -/
noncomputable def Job.supplyRow (dir : Bool) (t : Fin 4)
    (hit : party = ShrinkSurvivingOperands.party side t dir) (i : Fin (sub t)) :=
  ShrinkSurvivingColumn.row X side sub (width) slots m t dir (J.half dir t hit) J.arena
    J.node (J.scratch.surviving dir t) (J.allocation.row (idx, t)) i

/-- Concrete field, address, offsets and bits at every visit of the party scan. -/
noncomputable def Job.row : (c : At party side) → Fin (frames count sub c.val) → ResidentColumn.Row
  | ⟨none, h⟩, i => J.abRow (decide (party = 1)) (by simpa using ab_hit h) i
  | ⟨some (dir, t), h⟩, i => J.supplyRow dir t (supply_hit dir t h) i

/-- All input packet cells lie before staging and all staged widths fit their designated strides. -/
structure Job.Packets (endAddr : ℕ) (priv : Word w → Word w) : Prop where
  old : ∀ dir hit, ShrinkOldHalves.PlacedPackets X side J.arena J.nodes priv
    (ShrinkOldHalves.abSite X m dir) (J.abHalf dir hit) endAddr
  oldEnd : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.staging
  parentFit : (Packet.mk J.node (packed (outState) atSite J.parent)).Fits J.arena w endAddr
  parentStored : (Packet.mk J.node (packed (outState) atSite J.parent)).Stored J.arena
    (DFS.scratch endAddr priv)
  parentEnd : J.arena.base J.node + (packed (outState) atSite J.parent).length ≤ J.scratch.staging
  abStride : abWidth ≤ J.scratch.stride
  abRoom : J.scratch.staging + abWidth < 2 ^ w
  supplyStride : ∀ t, (width) m t ≤ J.scratch.stride
  supplyRoom : ∀ dir t, J.scratch.surviving dir t + (width) m t < 2 ^ w

set_option maxHeartbeats 800000 in
-- Check the selected graph against the dependent site and half-word coordinates.
private theorem Job.conditions {endAddr : ℕ} {priv : Word w → Word w}
    (ps : J.Packets endAddr priv) (c : At party side) (i : Fin (frames count sub c.val)) :
    (J.row c i).reads priv ∧ (J.row c i).Fits w J.scratch.staging ∧
      InBuffer J.scratch J.row c i := by
  rcases c with ⟨_ | ⟨dir, t⟩, h⟩
  · let dir := decide (party = 1)
    have hit : party = if dir then 1 else 0 := by simpa [dir] using ab_hit h
    let x := J.abHalf dir hit
    have stored := ps.old dir hit
    refine ⟨ShrinkAB.Physical.reads X m J.arcFit J.bucketFit i J.arena J.nodes side dir x
      priv stored, ShrinkAB.Physical.fits X m J.arcFit J.bucketFit i J.arena J.nodes side dir x
      J.scratch.staging ps.oldEnd le_rfl ps.abRoom stored, ?_⟩
    apply inBuffer_of J.scratch J.row _ i rfl
    intro hp
    exact (ab_bound X m J.arcFit J.bucketFit i J.arena J.nodes side dir x J.first
      J.scratch.staging hp).trans ps.abStride
  · let hit := supply_hit dir t h
    let z := J.half dir t hit
    let bank := J.allocation.row (idx, t)
    let dst := J.scratch.surviving dir t
    have same := J.packed_half dir t hit
    refine ⟨ShrinkSurvivingColumn.reads X side sub (width) slots m t dir z J.arena J.node dst bank
      priv (same.symm ▸ ps.parentFit) (same.symm ▸ ps.parentStored) i,
      ShrinkSurvivingColumn.fits X side sub (width) slots m t dir z J.arena J.node dst bank
        ready.count_pos J.scratch.staging (same.symm ▸ ps.parentEnd) (Nat.le_add_right _ _)
        (ps.supplyRoom dir t) i, ?_⟩
    apply inBuffer_of J.scratch J.row _ i rfl
    exact fun _ ↦ (surviving_bound X side sub (width) slots m t dir z J.arena J.node dst bank
      ready.count_pos i).trans (ps.supplyStride t)

variable (O : ShrinkCallHeader.Operands) (nodeExpr : PhaseRecipe.Expr)
variable (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)

/-- Construct the surviving gather operands for one orientation and role using the old level,
motif, parent node, and the role's staging destination. -/
def supplyInputs (a : ℕ) (dir : Bool) (t : Fin 4) :=
  ShrinkSurvivingSelected.inputs a O.level O.motif O.arguments O.argumentStride nodeExpr
    ((O.inputs a).surviving dir t)

/-- Generate the native register setup for each active AB or surviving copy at this party,
using the old and new degree exponents. -/
noncomputable def setups (a b : ℕ) (party : Fin 6) (layout : Bool) :=
  let d := 2 ^ a
  let c := Shrink.colors a
  let profile := subdivisions d c (2 ^ b)
  ShrinkPartyColumns.setup party layout (2 ^ c * d / 4) profile d (2 ^ b) (pieceCount d c)
    (O.cdHeader a).fields (supplyInputs O nodeExpr a)

/-- Old-level columns, ranked original ID lists and the selected AB interval bank. -/
structure Job.OldPublished (level : Word w) (T : IncidenceDirectory w) (origin : ℕ) : Prop where
  levelData : ShrinkCallHeader.Level X F sel level mem T origin J.older J.pitch J.first
  live : ShrinkCallHeader.Live X m O pub state level mem J.arena J.scratch.hidden J.scratch.stride
    J.scratch.hist
  motifCount : J.scratch.motifs = ShrinkTermInputs.motifCount X
  tables : ShrinkCallHeader.OldTables X mem T origin
  space : (ShrinkInput.plan X origin).stop < 2 ^ w
  allocation : ShrinkABSliceTable.Layout (ShrinkInput.thickBank X T origin)
    (ShrinkInput.piecesBank X T origin) buckets count pieces J.first
  bankWords : IndexedStarts.Stored (ShrinkABSliceTable.bank (w := w) J.first count pieces
    (BundleLists.portIndex (Shrink.packedIndex (a := a) (g := g) X.baseIndex)
      (X.packingData.bundle m)).val)
    (ShrinkSliceArrays.thickWidths X.packingData X.shrinkOrder X.packingWidth
      (X.packingData.bundle m))
    (ShrinkSliceArrays.abWidths X.packingData X.shrinkNumber X.packingWidth
      (X.packingData.bundle m)) mem

/-- The common selected slot and interval images. The per-endpoint destinations are the
staging expressions in the very same six-party call header. -/
structure Job.SupplyPublished (heads : SlotLevel.Heads) (absolute : Word w)
    (U : IncidenceDirectory w) (layer pitch : ℕ) : Prop where
  tableHeads : ∀ dir t, ShrinkSurvivingSelected.Published X (supplyInputs O nodeExpr a dir t).tables
    m heads absolute (b := b) (pub := pub) (state := state) (mem := mem)
  directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absolute mem
  sorted : Build.OrderedTables X ready side heads mem
  absFit : absolute.val + (idx).val < 2 ^ w
  slotFit : finish (levelShape (b := b) X) heads < 2 ^ w
  degreeFit : 2 ^ b < 2 ^ w
  twoFit : 2 < 2 ^ w
  allocation : J.allocation.Fits
  images : ∀ i, Image (J.allocation.row i)
    (selected X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) J.allocation
      F X.packingWidth sel i) mem
  half : ∀ dir t, (supplyInputs O nodeExpr a dir t).half.Stored U J.arena layer pitch pub state mem
  incidence : U.ActualColumns (outState) mem
  capacity : Fintype.card (outState).Base * 2 ^ g * 2 ^ b ≤ 2 ^ w
  nodeWord : nodeExpr.eval pub state mem = (J.node : Word w)
  destination : ∀ dir t, ((O.inputs a).surviving dir t).eval pub state mem =
    (J.scratch.surviving dir t : Word w)
  interval : ∀ dir t, (supplyInputs O nodeExpr a dir t).tables.intervalHead.eval pub state mem =
    (J.allocation.widthEnd : Word w)

variable {level absolute : Word w} {T U : IncidenceDirectory w} {origin layer pitch : ℕ}
variable {heads : SlotLevel.Heads}
variable (old : J.OldPublished O pub state mem level T origin)
variable (next : J.SupplyPublished O nodeExpr pub state mem heads absolute U layer pitch)

set_option maxHeartbeats 1000000 in
-- Reduce the packed site, actual endpoint row and the level's stored numbering together.
include old next in
private theorem Job.recorded (c : At party side) (i : Fin (frames count sub c.val)) :
    (J.row c i).Recorded (setups O nodeExpr a b party side c i) pub state mem := by
  rcases c with ⟨_ | ⟨dir, t⟩, hc⟩
  · let dir := decide (party = 1)
    have hit : party = if dir then 1 else 0 := by simpa [dir] using ab_hit hc
    have scratchEq : ShrinkCallHeader.scratch X J.scratch.hidden J.scratch.stride J.scratch.hist =
        J.scratch := by
      unfold ShrinkCallHeader.scratch
      rw [← old.motifCount]
    have h := ShrinkCallHeader.ab_recorded X F sel m O pub state level mem J.arena T origin
      J.older J.pitch J.first J.scratch.hidden J.scratch.stride J.scratch.hist
      old.levelData old.live old.tables old.space old.allocation old.bankWords dir
      (J.abHalf dir hit) i
    dsimp only at h
    rw [scratchEq] at h
    exact h
  · exact ShrinkSurvivingSelected.recorded X ready m t dir i F sel J.term J.stride J.widthBase
      (supplyInputs O nodeExpr a dir t) heads absolute U J.arena J.node (J.scratch.surviving dir t)
      layer pitch (J.half dir t (supply_hit dir t hc)) (next.tableHeads dir t) next.directory
      next.sorted next.absFit next.slotFit next.degreeFit next.twoFit next.allocation next.images
      (next.half dir t) next.incidence next.capacity next.nodeWord (next.destination dir t)
      (next.interval dir t)

private noncomputable def widths (m' : X.packingData.Motif) (e : Bool × Fin 4) : ℕ :=
  X.packingData.termWidths F X.shrinkNumber X.packingWidth sel m' e.1 e.2

/-- Values consumed by the demand and supply map readers after all frames execute. -/
structure Job.Assembled (before after : Word w → Word w) : Prop where
  retained : ShrinkCallSupplyCells.Retained X side sub (widths (F := F) (sel := sel)) slots
    m party J.scratch J.parent before after
  ab : ∀ (dir : Bool) (hit : party = if dir then 1 else 0) (i : Fin abWidth),
    after ((J.scratch.staging + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (ShrinkCallDemandCells.abBit X side m dir (hit ▸ J.old) i)
  below : ∀ x : Word w, x.val < J.scratch.staging → after x = before x

set_option maxHeartbeats 800000 in
-- Identify both orientations of the selected new half with the typed map's local arguments.
private theorem Job.assembled {before after : Word w → Word w} {endAddr : ℕ}
    (ps : J.Packets endAddr before)
    (staged : ∀ c : At party side, ∀ addr : Word w, base J.scratch c.val ≤ addr.val →
      addr.val < base J.scratch c.val + J.scratch.stride →
        after addr = ResidentColumn.writes (J.row c) (List.finRange _) before addr)
    (below : ∀ x : Word w, x.val < J.scratch.staging → after x = before x) :
    J.Assembled before after := by
  refine ⟨?_, ?_, below⟩
  · intro dir t hit site halves dst i
    have active : some (dir, t) ∈ columns party side := by
      apply (mem_columns ..).mpr
      change decide (party = ShrinkCallFields.supplyParty dir (side, t)) = true
      apply decide_eq_true
      cases dir <;> exact hit
    let c : At party side := ⟨some (dir, t), active⟩
    let addr : Word w := ((dst + i.val : ℕ) : Word w)
    have hlt : i.val < (width) m t := i.isLt
    have val : addr.val = dst + i.val := Nat.mod_eq_of_lt (by
      have room := ps.supplyRoom dir t
      change dst + (width) m t < 2 ^ w at room
      omega)
    apply staged c addr (by rw [val]; exact Nat.le_add_right _ _) ?_
    change addr.val < dst + J.scratch.stride
    rw [val]
    exact Nat.add_lt_add_left (hlt.trans_le (ps.supplyStride t)) _
  · intro dir hit i
    have active : none ∈ columns party side := by
      apply (mem_columns ..).mpr
      change decide (party = 0 ∨ party = 1) = true
      cases dir <;> simp_all
    let c : At party side := ⟨none, active⟩
    let addr : Word w := ((J.scratch.staging + i.val : ℕ) : Word w)
    have val : addr.val = J.scratch.staging + i.val :=
      Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans ps.abRoom)
    refine (staged c addr (by rw [val]; exact Nat.le_add_right _ _)
      (by rw [val]; exact Nat.add_lt_add_left (i.isLt.trans_le ps.abStride) _)).trans ?_
    have wd := ShrinkCallDemandCells.ab_written X side m J.arena J.nodes dir (hit ▸ J.old)
      J.arcFit J.bucketFit J.first J.scratch.staging before ps.abRoom.le i
    cases dir <;> subst party <;> exact wd

local notation "setupAt" => setups O nodeExpr a b party side
local notation "flatSetup" => gather party side count sub setupAt
local notation "flatRow" => gather party side count sub (Job.row J)

open private writes_congr from OAI.Computability.VPVNP.PairShrinkPartyColumns

/-- The native update restricted to the upper private scratch. -/
noncomputable def Job.updated (endAddr : ℕ) (before : DFS.Scratch w endAddr) :
    DFS.Scratch w endAddr :=
  DFS.scratch endAddr (ResidentColumn.writes flatRow (List.finRange _) (rawScratch before))

/-- The public trace of a fixed resident job. -/
noncomputable def Job.trace :=
  ResidentColumn.trace flatSetup flatRow (List.finRange _) pub state mem

include old next in
/-- The installed rows return the typed map fields, the exact chronological trace and the
upper-scratch update. Private cells below the stack boundary are preserved. -/
theorem native_party_reads {p r k : ℕ} (M : Machine w p r k)
    (vm : ∀ i, Fin (RegisterSetup.regCount ((flatSetup i).operands)) ↪ Fin r)
    (inputs : Fin 6 → Fin r) (loc : ResidentColumn.Label flatSetup → Fin p) (ret : Fin p)
    (code : ∀ l, M.code (loc l) = ResidentColumn.instruction flatSetup vm inputs loc ret l)
    (safe : ∀ i v j, vm i v ≠ inputs j)
    (allowed : ℕ → Prop) (sites : ∀ c i, (J.row c i).ReadSafe (setupAt c i) allowed pub state mem)
    (cfg : Config w p r) (entry : cfg.pc = ResidentColumn.start flatSetup loc ret 0)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    {endAddr : ℕ} (ps : J.Packets endAddr cfg.privateMem) :
    let es := J.trace O nodeExpr pub state mem
    ∃ out, ResidentColumn.Result flatSetup vm M ret flatRow
      (List.finRange (visits party side count sub).length) mem cfg out es ∧
      J.Assembled cfg.privateMem out.privateMem ∧ SourceTransport.Reads allowed es ∧
      DFS.scratch endAddr out.privateMem = J.updated endAddr (DFS.scratch endAddr cfg.privateMem) ∧
      (∀ a : Word w, a.val < endAddr → out.privateMem a = cfg.privateMem a) := by
  intro es
  obtain ⟨out, res, reads⟩ := ResidentColumn.native_exact M loc ret code safe flatRow mem pub state
    (fun _ ↦ J.recorded O nodeExpr pub state mem old next _ _) J.scratch.staging
    (fun _ ↦ (J.conditions ps _ _).2.1) allowed (fun _ ↦ sites _ _) cfg entry hp hs
    (fun _ ↦ (J.conditions ps _ _).1)
  have eqMem := res.memory
  have staged := ShrinkPartyColumns.memory J.scratch J.row J.scratch.staging
    (fun c i ↦ (J.conditions ps c i).2.1) (fun c i ↦ (J.conditions ps c i).2.2) cfg.privateMem
  have assm := J.assembled (after := out.privateMem) ps
    (fun c a lo hi ↦ (congrFun eqMem a).trans (staged.1 c a lo hi))
    (fun a below ↦ (congrFun eqMem a).trans (staged.2 a below))
  refine ⟨out, res, assm, reads, ?_, ?_⟩
  · funext a
    change out.privateMem a.val = ResidentColumn.writes flatRow (List.finRange _) _ a.val
    rw [eqMem]
    exact writes_congr _ _ a.val (by simp [rawScratch, a.property, DFS.scratch])
  · intro a ha
    apply assm.below
    have first : endAddr ≤ J.arena.base J.node := ps.parentFit.1
    have last := ps.parentEnd
    omega

include old next in
/-- Run every real AB and surviving frame of the selected resident map, in one linked program.
The resulting private state supplies the bits of its typed matrix call. -/
theorem native_party {p r k : ℕ} (M : Machine w p r k)
    (vm : ∀ i, Fin (RegisterSetup.regCount ((flatSetup i).operands)) ↪ Fin r)
    (inputs : Fin 6 → Fin r) (loc : ResidentColumn.Label flatSetup → Fin p) (ret : Fin p)
    (code : ∀ l, M.code (loc l) = ResidentColumn.instruction flatSetup vm inputs loc ret l)
    (safe : ∀ i v j, vm i v ≠ inputs j)
    (cfg : Config w p r) (entry : cfg.pc = ResidentColumn.start flatSetup loc ret 0)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    {endAddr : ℕ} (ps : J.Packets endAddr cfg.privateMem) :
    ∃ events out, ResidentColumn.Result flatSetup vm M ret flatRow
      (List.finRange (visits party side count sub).length) mem cfg out events ∧
        J.Assembled cfg.privateMem out.privateMem := by
  obtain ⟨ev, out, run, staged, below⟩ := ShrinkPartyColumns.native J.scratch J.row
    J.scratch.staging (fun c i ↦ (J.conditions ps c i).2.1)
    (fun c i ↦ (J.conditions ps c i).2.2) setupAt M vm inputs loc ret code safe
    mem pub state (J.recorded O nodeExpr pub state mem old next) cfg entry hp hs
    (fun c i ↦ (J.conditions ps c i).1)
  exact ⟨ev, out, run, J.assembled ps staged below⟩

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI

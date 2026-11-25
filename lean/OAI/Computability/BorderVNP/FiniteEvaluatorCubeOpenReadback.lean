import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenSuffix
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostDest
import OAI.Computability.BorderVNP.FiniteEvaluatorPublicPhase

/-! # Opening the physical cube evaluator on the returned private word

The native owner traversal publishes the true directory count and packet
banks. The four following stages use the actual receiving-cell bank and
packed cable widths. The same cube lookup is ready at the end of the open
phase on every returning path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OpenSuffix

open VPVNP.BurstRAM BorderVNP.Cube RoutingISA

/-- Exact decomposition of the finite evaluator's opening code. -/
theorem openCells_eq {n b h K s : ℕ} {F : Type*} [Fintype F] (table : TableEntry n b h K s → F) :
    openCells table = .seq (CubeDeck.install table) (.seq (TeamRows.ownedGroups n b h K s) code) := rfl

/-- All four suffix stages run without consuming further private choices or sign bits. -/
theorem unsigned : code.unsigned = true := by decide

/-- Readable numerical controls for the receiving cells and compact output arrays. -/
structure Placement (H : Inputs) (a : CubeArena.Layout) (allocated : DiagonalTallyAllocation.BeforeTasks)
    (base : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Frame word 72 points to the real two-word receiving-cell directory. -/
  pointer : mem (base+72) = a.hostDirectory
  /-- Each second directory word is the address of its actual receiving-cell bank. -/
  bank : ∀ c < a.cells, mem (a.hostDirectory+2*c+1)=a.cellBank+c*a.cellStride
  /-- Every owned endpoint of a delivered cable fits the assigned receiving-cell stride. -/
  ends : let host := HostScatter.Layout.fromFrame base mem
    ∀ i < host.count, ∀ side, host.Owned mem i side →
      host.cell mem i side < a.cells ∧ mem (host.relative+2*i+side.toNat)+host.width mem i ≤ a.cellStride
  /-- Compacted per-cell range directory in the report reservation. -/
  ranges : H.bundles.ranges = allocated.ranges
  /-- Six-word bundle rows in the same report reservation. -/
  bundles : H.bundles.output = allocated.bundleTable
  /-- Four-word owned-cell control array. -/
  four : H.control.four = allocated.four
  /-- Six-word owned-cell control array. -/
  six : H.control.six = allocated.six

variable {w n b h K d : ℕ} {F : Type*} (H : Inputs) (a : CubeArena.Layout)
variable (allocated : DiagonalTallyAllocation.BeforeTasks) (deckEnd : ℕ)
variable (P : CubePacket.Inputs n b h K d F) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {r z : Bank w} {mem out : Memory w} {es : List (TeamRAM.Event w)}

/-- Physical receiving-cell geometry and a report reservation anywhere past the
field deck suffice for all the addressed inputs, including on the signed task arena. -/
theorem placed_words (ready : Ready H (pub 0).val (readings mem) w)
    (placed : Placement H a allocated (pub 0).val (readings mem))
    (returned : Runs pub mac code r mem es z out)
    (low : (pub 0).val+112 ≤ a.header.packetBase) (past : a.stop ≤ deckEnd) (start : deckEnd ≤ allocated.start)
    (location : ∀ x, CubePacket.ReadAt P pub x → (∃ j ∈ CubePacket.frameWords, x=(pub 0).val+j) ∨
      (a.header.packetBase ≤ x ∧ x<a.cellBank) ∨ (a.stop ≤ x ∧ x<deckEnd)) :
    ∀ x, CubePacket.ReadAt P pub x → out x=mem x :=
  cube_words H P a deckEnd ready returned low past location
    (CubeAllocation.host_dest a (pub 0).val (readings mem) placed.pointer placed.bank placed.ends)
    (afterDeck_of_allocation H allocated start placed.ranges placed.bundles placed.four placed.six)

/-- On the genuine memory from the owned traversal the padding test supplies
the precise success condition. The remainder uses no private choices, and
its final memory retains the complete lookup. -/
theorem placed_run [Fintype F] (original : CubePacket.Prepared P pub mem)
    (ready : Ready H (pub 0).val (readings mem) w)
    (placed : Placement H a allocated (pub 0).val (readings mem))
    (valid : (Padding.Layout.fromFrame (pub 0).val (readings mem)).Valid (readings mem))
    (low : (pub 0).val+112 ≤ a.header.packetBase) (past : a.stop ≤ deckEnd) (start : deckEnd ≤ allocated.start)
    (location : ∀ x, CubePacket.ReadAt P pub x → (∃ j ∈ CubePacket.frameWords, x=(pub 0).val+j) ∨
      (a.header.packetBase ≤ x ∧ x<a.cellBank) ∨ (a.stop ≤ x ∧ x<deckEnd)) :
    Owned.TraceRun pub mac code r mem [] (H.cost (pub 0).val (readings mem))
      (fun _ mt => readings mt=H.image (pub 0).val (readings mem) ∧ CubePacket.Prepared P pub mt) := by
  obtain ⟨events,last,mt,path,ok,cost,image⟩ := Owned.traceRun_unsigned ((run H ready).complete valid) unsigned
  exact ⟨events,last,mt,path,ok,cost,image,original.transfer P
    (placed_words H a allocated deckEnd P ready placed path low past start location)⟩

end FiniteEvaluator.OpenSuffix

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical FiniteEvaluator RoutingISA VPVNP.BurstRAM DiagonalTallyPacketEmit
open scoped Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R) (t : Fin (R+1))
variable (header profile cells cables maxRows stride : ℕ)
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable (B : DiagonalTallyAllocation.Bounds) (l : TypedTaskBuilder.Layout) (sw bw : ℕ)
variable (pub : Arg → Word w)

local notation "arena" => planArena L R header profile cells cables maxRows stride
local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "number" => Fin.val ∘ V.owners R (Sigma.fst (Prod.fst raw))
local notation "packet" => CubeHeaderInstall.Inputs.packetBase (CubeArena.Layout.header arena)
local notation "single" => CubeArena.Layout.singleBank arena
local notation "A" => bankData V R raw packet single
local notation "scan" => CubeArena.Layout.scanner arena (Fin.val (pub 0)) (Fin.val t) (Fin.val axis) (CubeArena.Layout.rowSelectorBits arena)
local notation "vbase" => CubeArena.Layout.vertexBase arena
local notation "stop" => CubeArena.Layout.publicBase arena
local notation "power" => CubeArena.Layout.powerBase arena
local notation "fresh" => CubeArena.Layout.stop arena
local notation "f" => CubeAllocation.frame arena table B l sw bw (List.length (teamPairs V R raw t))
local notation "dst" => DiagonalTallyAllocation.AfterTasks.ids (CubeAllocation.after arena table B l sw bw)
local notation "ptr" => CubeConstants.idBase fresh L.dimension L.bitWidth L.copies L.alternatives L.supply
local notation "Y" => cubeInputs V R raw t packet f rfl table fresh dst
local notation "deckEnd" => CubeConstants.arenaEnd fresh (CubeDeck.entry table)
local notation "reports" => CubeAllocation.before arena table B

variable (H : OpenSuffix.Inputs)
variable {mac : TeamOpcode.Macros w 8} {r z : Bank w} {es : List (TeamRAM.Event w)} {mem out : Memory w}

/-- Every word needed for the actual routed lookup survives all four stages of
the opening suffix, using the word addresses of its assigned host and report banks. -/
theorem open_cube_words (first : (pub 0).val+112 ≤ header)
    (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
    (placed : OpenSuffix.Placement H arena reports (pub 0).val (readings mem))
    (returned : Runs pub mac OpenSuffix.code r mem es z out) :
    ∀ x, CubePacket.ReadAt Y pub x → out x = mem x := by
  have low : (pub 0).val+112 ≤ packet := first.trans (by unfold CubeHeaderInstall.Inputs.packetBase; change header ≤ header+13+2*_+_; omega)
  have past : fresh ≤ deckEnd := by unfold CubeConstants.arenaEnd CubeConstants.idBase; omega
  exact OpenSuffix.placed_words H arena reports deckEnd Y ready placed returned low past le_rfl
    (fun _ read => V.cubeRead_location R raw t header profile cells cables maxRows stride table B l sw bw pub read)

/-- The end of the actual owned-group scan and any return through all remaining
opening instructions together supply the complete pre-cell lookup in its final
word memory. All operand addresses are recovered from the given routed word. -/
theorem cube_ready_after_open (initial : Memory w)
    (observed : CubeTriple.Readback (l:=scan) A number power vbase stop initial mem)
    (boot : CubeDeck.At table f fresh (readings initial))
    (initialFrame : Frame.resident {f with count:=readings initial ((pub 0).val+46)} (readings pub) (readings initial))
    (tableWord : readings initial ((pub 0).val+47)=ptr) (dstWord : readings initial ((pub 0).val+71)=dst)
    (first : (pub 0).val+112 ≤ header) (word : (CubeAllocation.after arena table B l sw bw).packed ≤ 2^w)
    (ready : OpenSuffix.Ready H (pub 0).val (readings mem) w)
    (placed : OpenSuffix.Placement H arena reports (pub 0).val (readings mem))
    (returned : Runs pub mac OpenSuffix.code r mem es z out) :
    CubePacket.Prepared Y pub out ∧ CubePacket.Sources Y (CubeAllocation.tasks arena table B l sw bw) := by
  obtain ⟨original,sources⟩ := V.cube_ready_of_readback R raw t header profile cells cables maxRows stride table B l sw bw
    pub initial mem observed boot initialFrame tableWord dstWord first word
  exact ⟨original.transfer Y (V.open_cube_words R raw t header profile cells cables maxRows stride table B l sw bw
    pub H first ready placed returned),sources⟩

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI

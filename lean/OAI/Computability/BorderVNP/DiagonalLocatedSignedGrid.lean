import OAI.Computability.BorderVNP.DiagonalChosenSignedCalendar
import OAI.Computability.BorderVNP.DiagonalGridReportRoom
import OAI.Computability.BorderVNP.DiagonalFixedSignedWitness
import OAI.Computability.BorderVNP.DiagonalSignedPacketAdmission
import OAI.Computability.BorderVNP.DiagonalSeedLiteralRange
import OAI.Computability.BorderVNP.DiagonalFrozenPacketNumerals
import OAI.Computability.BorderVNP.DiagonalFrozenSuppliedRoom
import OAI.Computability.BorderVNP.DiagonalFrozenGridProcessors
import OAI.Computability.BorderVNP.PackedFrozenHistoryCapacity
import OAI.Computability.BorderVNP.PackedFrozenNativePort

/-! # The selected signed seed grid and the physical directory used by its frozen table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Cover Epoch Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open Shortening.PublicCapacity EnrichedOuter ExternalSew TeamScales TeamContraction ProcessorSlots RoutingISA RoutingISA.Evaluator
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar FieldProcessor
open scoped Classical BorderVNP.Epoch.Cube

set_option maxHeartbeats 1600000
set_option maxRecDepth 6000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {G : PaidIdentity F D m}
    {S : SiteSchedule G} (cube : FixedCube K) {extra E deg Q A B j : ℕ}
    {scales : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} scales (E+1) deg Q A B j)
    (header n : ℕ)

local notation "batch" => stretch b.ρ n
local notation "axes" => Fintype.card (Epoch.Cube D)
local notation "start" => CoverScale.initialDepth (Epoch.Cube D) batch n
local notation "depth₀" => start-1
local notation "tileCount₀" => GridHosts.tileCount axes depth₀
local notation "tileBlock" => GridHosts.inputBlockWidth batch n axes depth₀
local notation "epochs₀" => epochs scales.τ n
local notation "copies₀" => width n scales.α
local notation "teams₀" => b.physical.teamsPred n
local notation "link₀" => b.physical.link n
local notation "word₀" => b.physical.word n
local notation "xi" => (scales.τ:ℝ)/5

/-- Public dimensions, source-storage ceilings and the two compatible
packet admissions on the same rounded signed grid, before any input pin. -/
structure LocatedSignedGridAt : Prop where
  /-- Reinsert the initial frozen-grid layer. -/
  depth_eq : depth₀+1 = start
  /-- The deck index enumerates precisely the initial sites. -/
  tiles_eq : tileCount₀ = CoverScale.sites (Epoch.Cube D) start
  /-- The replicated output teams fill the physical processor array. -/
  count : (fan S)^epochs₀*copies₀ = teams₀+1
  /-- Each input block has a physical address. -/
  block_pos : 0 < tileBlock
  /-- The unrounded input ports fit the chosen physical link. -/
  block_le : tileBlock ≤ link₀
  /-- At least one bit is available per public logarithm. -/
  log_pos : 1 ≤ logWidth batch n
  /-- Public word width is the phase-degree power used by the packet budget. -/
  word_eq : word₀ = (logWidth batch n)^(E+2)
  /-- The arithmetic link length agrees with the physical processor scale. -/
  link_eq : link₀ = TeamScales.link xi (teams₀+1) n
  /-- The final shape still contains a port of the initial grid. -/
  sites_pos : 0 < (boundaryShape S (depth₀+1) epochs₀).sites
  /-- The seed description and record fields fit the storage ceiling. -/
  geometricStorage : SeedStorage axes n batch depth₀ copies₀ epochs₀ (fan S) S.recordFactor header scales.α
  /-- The public seed program fits the same storage ceiling. -/
  programStorage : SeedStorage axes n batch depth₀ copies₀ epochs₀ (fan S) S.publicProgramFactor header scales.α
  /-- Original descriptor words, body capacities and the complete
  retransmitted literal volume fit the actual processor tail. -/
  literalRanges :
    let capacity := seedBoxCapacity n batch axes depth₀ (Fintype.card (Direction axes))
    let desc := seedDescriptionWidth n batch axes depth₀ (header*logWidth batch n) (BottomGridBank.bodyBudget capacity)
    let tail := literal scales.α n/2
    0<tail ∧ capacity≤n ∧ desc≤n ∧ desc≤tail ∧
      ((fan S)^epochs₀*tileCount₀)*desc≤(teams₀+1)*batch*tail
  /-- The native field, count vector and factor header fit on the actual
  paid/cube scalar numbering. The chosen hardware word extends the short
  chronology width in the packet input certificate. -/
  packetNumerals :
    let mass := S.publicProgramFactor^epochs₀*initialMass (D:=D) n batch depth₀ copies₀ header
    let birth := max 2 (max copies₀ (seedBoxCapacity n batch axes depth₀ (Fintype.card (Direction axes))))
    let coefficient := (birthWordCoefficient G+8)*(BankCharges.bound G+1)*(S.populationFactor+2)
    let scalar := max (15*mass) (boundary S (depth₀+1) epochs₀).sites +
      max (max birth (coefficient*(mass+1))) (max 1 (15*mass))+1
    let hooks := Fintype.card (G.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    ∀ w ≥ 60*logWidth batch n,
      FrozenPacketNumerals G (fun z => cube.scalarNumber G (.inl z)) hooks (header*logWidth batch n) w scalar mass

  /-- The same label rows admit the boundary packets for this physical team count. -/
  packets : ∀ work, ∀ plan : SeedPlan S n batch depth₀ epochs₀ copies₀ header work,
    ∃ labels : plan.SignedLabelRows count link₀ (cube.pred+1) scales.α xi,
      plan.AdmitsSignedPackets cube scales.α xi count labels

  /-- The actual sewn private grid bounds every cell's supplied words. -/
  cellLoads : ∀ work, ∀ plan : SeedPlan S n batch depth₀ epochs₀ copies₀ header work,
    plan.SewnCellLoads count link₀
  /-- The real per-cell stride includes the original descriptors, supplied
  words, report gap and the final one-word sentinel. -/
  placementSpan :
    let bytes := seedDescriptionWidth n batch axes depth₀ (header*logWidth batch n)
      (BottomGridBank.bodyBudget (seedBoxCapacity n batch axes depth₀ (Fintype.card (Direction axes))))
    ∀ gap supplied, gap≤n^2 → supplied≤TeamScales.width n (1/5:ℝ) →
      supplied+gap+((fan S)^epochs₀*tileCount₀)*bytes≤3*(batch*n)^2+1

  /-- Each actual processor has a distinct slot among the initial grid tiles. -/
  processors_le_tiles : batch≤tileCount₀
  /-- The enlarged phase degree gives enough room for every actual report
  source, counted with the selected grid depth and copy multiplicity. -/
  issuedReportScale : E+2 ≤ deg → GridReportScaleAt cube b header n
  /-- The numbered grammar labels of this very batch fit its physical word. -/
  labelFit : Branch.pairedTableParameters n (stretch b.σ n) ≤ 2^word₀

/-- All of these equalities and admissions hold on the same sufficiently
large lengths. The final site bound follows directly from the original
port rectangle retained at every epoch. -/
theorem JointSchedule.eventually_located_signed_grid : ∀ᶠ n : ℕ in atTop, LocatedSignedGridAt cube b header n := by
  filter_upwards [b.eventually_signed_grid,b.eventually_signed_packet_admission cube header,
    b.eventually_geometricSeedStorage header,b.eventually_programSeedStorage header,b.eventually_seedLiteralRanges header,
    b.eventually_frozen_packet_numerals header (Fintype.card (G.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width))
      (fun z => cube.scalarNumber G (.inl z)),b.eventually_signedSewnCellLoads header,
    b.eventually_frozen_supplied_directory header,b.eventually_frozen_grid_processors,eventually_ge_atTop 1,
    b.eventually_gridReportScale cube header,b.eventually_gridMarkWidths]
    with n grid admitted geom stored literalFit numerals loads placement procs hn report marks
  let r := stretch b.ρ n
  let h := CoverScale.initialDepth (Epoch.Cube D) r n
  let d := h-1
  have depth : d+1=h := Nat.sub_add_cancel (show 1≤h from Nat.succ_pos _)
  have tiles := (seedPortCount (D:=D) d).trans (congrArg (CoverScale.sites (Epoch.Cube D)) depth)
  have log : 1 ≤ logWidth r n := by
    rw [Shortening.PublicCapacity.public_logWidth]
    have hr : 1 ≤ r := stretch_one b.ρ n
    have pair : 1 ≤ n*r := Nat.mul_le_mul hn hr
    have two : 2 ≤ 2*n*r := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 pair
    exact (Nat.clog_mono_right 2 two).trans' (by decide)
  have physical := b.sizes hn
  have link := physical.2.1.trans (congrArg (fun R => TeamScales.link ((scales.τ:ℝ)/5) R n) physical.1.symm)
  have sites := (FrozenTape.ports_fit S (d+1)).1 (epochs scales.τ n)
  have live : 0 < (S.fanIn^S.rounds)^(epochs scales.τ n)*CoverScale.sites (Epoch.Cube D) (d+1) :=
    Nat.mul_pos (pow_pos (pow_pos S.positiveFanIn _) _) Fintype.card_pos
  refine ⟨depth,tiles,grid.1,grid.2.1,grid.2.2,log,physical.2.2.1,link,live.trans_le sites,geom,stored,literalFit,numerals,?_,?_,placement,procs,report,marks.1⟩
  · intro work plan
    obtain ⟨_,labels,packets⟩ := admitted work plan
    exact ⟨labels,packets⟩
  · intro work plan
    exact (loads work plan).choose_spec

variable {cube b header n}

/-- Every original power bit uses a shift below the word width of this grid. -/
theorem LocatedSignedGridAt.wordFit (grid : LocatedSignedGridAt cube b header n) :
    logWidth (stretch b.ρ n) n ≤ b.physical.word n := by
  rw [grid.word_eq]
  exact Nat.le_self_pow (by omega) _

/-- Physical sites, cable blocks and retained source bundles in the selected
directory on a wiring whose true program-plus-literal length is known. -/
theorem LocatedSignedGridAt.directory (grid : LocatedSignedGridAt cube b header n)
    {time pins ell inner : ℕ} {Edge : Type} (wiring : Wiring teams₀ batch time pins ell inner n Edge)
    (literalSize : wiring.program.length+time = literal scales.α n) (linkEq : ell=link₀) (desc : ℕ) :
    freeDirectory teams₀ batch (wiring.program.length+time) ell tileCount₀ tileBlock
      ((fan S)^epochs₀*tileCount₀) desc = b.signedStartupDirectory n desc := by
  unfold JointSchedule.signedStartupDirectory
  unfold GridHosts.inputBlockWidth
  rw [literalSize,linkEq,grid.tiles_eq]
  rfl

/-- The emitted packet inputs for the very directory read by the frozen
table, including its actual paid-scalar numbering. This instantiates the
calendar's directory bounds through the physical wiring identity. -/
theorem LocatedSignedGridAt.packet_inputs (grid : LocatedSignedGridAt cube b header n)
    (φ : K →+* F) (q : ℕ) (adv : ℕ → ℕ) (c k factor volume : ℕ)
    (checked : CalendarOutputAt cube b φ q adv c k factor volume n)
    {time pins ell inner : ℕ} {Edge : Type} (wiring : Wiring teams₀ batch time pins ell inner n Edge)
    (literalSize : wiring.program.length+time = literal scales.α n) (linkEq : ell=link₀)
    (order : Fin tileCount₀ ≃ (Fin axes → Deck (depth₀+2)))
    (position : (Fin axes → Deck (depth₀+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖≤1}) (desc : ℕ) :
    let sites := tileCount₀
    let origins := (fan S)^epochs₀*sites
    let dir := freeDirectory teams₀ batch (wiring.program.length+time) ell sites tileBlock origins desc
    let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S (depth₀+1) epochs₀)
    let g := Fintype.card (G.Entry ⊕ _root_.OAI.Computability.BorderVNP.Cube.TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    SignedPacketInputBounds S (depth₀+1) epochs₀ cells ((teams₀+1)*sites) (60*logWidth batch n) word₀
      (logWidth batch n) E volume g (Boundary.seedFormat wiring order position copies₀)
      {dir with sites := sites,entries := origins} rfl (fun z => cube.scalarNumber G (.inl z)) := by
  intro sites origins dir cells g
  have eqn : dir=b.signedStartupDirectory n desc := grid.directory wiring literalSize linkEq desc
  rw [eqn]
  exact (checked.2.2 wiring order position desc (fun z => cube.scalarNumber G (.inl z))).2

/-- The actual zero-tail tape registered before the field literals has the
source program length, both cut fields, sorter setup and complete free field.
Its directory therefore uses the same description width, tile numbers, and
replicated entries as the one used for the signed startup. -/
theorem LocatedSignedGridAt.template_directory {k : ℕ} (grid : LocatedSignedGridAt cube b header (k+1))
    (pins : ℕ) :
    let n := k+1
    let r := stretch b.ρ n
    let d := CoverScale.initialDepth (Epoch.Cube D) r n-1
    let tiles := GridHosts.tileCount (Fintype.card (Epoch.Cube D)) d
    let blockSize := GridHosts.inputBlockWidth r n (Fintype.card (Epoch.Cube D)) d
    let T := epochs scales.τ n
    let R := b.physical.teamsPred n
    let w := b.physical.word n
    let ξ := (scales.τ:ℝ)/5
    let link := TeamScales.link ξ (R+1) n
    let ec := Wires.sortExponent (block ξ n)
    let eval := signedBody (cube.cubeID G)
    let physical := cube.signedSiteProgram G
    let len := freeWidth physical scales.α 32 64 r w n
    let tail := setupWidth (w+1) n+(prefixCapacity r 32 64 w n+1+len)
    let time := TeamContraction.cutWidth n+tail
    let cap := seedBoxCapacity n r (Fintype.card (Epoch.Cube D)) d
      (Fintype.card (DeckGrid.Direction (Fintype.card (Epoch.Cube D))))
    let desc := seedDescriptionWidth n r (Fintype.card (Epoch.Cube D)) d (header*logWidth r n) (BottomGridBank.bodyBudget cap)
    ∀ geo : Scale physical ((withStartup eval).slots+1) 64 32 scales.α ξ r n R w ec,
      let template := tapeTemplate (R:=R) (r:=r) (regs:=64) (w:=w) (e:=ec) (width:=w+1)
        (link:=link) (k:=k) (a:=tail) physical geo.fits pins
      template.program.length+time = literal scales.α n ∧
        freeDirectory R r (template.program.length+time) link tiles blockSize ((fan S)^T*tiles) desc =
          b.signedStartupDirectory n desc := by
  intro n r d tiles blockSize T R w ξ link ec eval physical len tail time cap desc geo template
  have length : template.program.length+time=literal scales.α n := geo.literalSize
  exact ⟨length,grid.directory template length grid.link_eq.symm desc⟩

end Diagonal

end BorderVNP
end Computability
end OAI

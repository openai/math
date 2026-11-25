import OAI.Computability.BorderVNP.FiniteEvaluatorCubeReadLocation
import OAI.Computability.BorderVNP.CubeScatterPadding
import OAI.Computability.BorderVNP.CubeHostScatterProgram
import OAI.Computability.BorderVNP.PackedBundleDirectoryRun
import OAI.Computability.BorderVNP.RoutingISACellControlProgram

/-! # Physical cube operands across the four instructions following ownership

The padding test reads memory without changing it. The host scatter writes
only its owned cable intervals. The stable bundle directory writes ranges and
bundle rows. The control producer writes the four- and six-word owned tables
and frame word 90. These actual images leave the cube operands available
before the subsequent private report preparation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OpenSuffix

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube Packing

/-- The four fixed instructions following the completed native vertex scan. -/
def code : Code := .block [Padding.verify,HostScatter.program,BundleDirectory.program,CellControlRows.program]

/-- Actual marker-sorted bundle groups and the true tables addressed by the suffix. -/
structure Inputs where
  /-- The stable producer's input and output addresses. -/
  bundles : BundleDirectory.Layout
  /-- Original six-word headers in each cell's sorted order. -/
  groups : ℕ → List BottomReports.BundleHeader
  /-- Width of the physical sorted array. -/
  sortWidth : ℕ
  /-- Addresses of the six-word and four-word per-owned-cell control rows. -/
  control : CellControlRows.Layout

variable {w : ℕ} (H : Inputs) (base : ℕ) (initial : ℕ → ℕ)

/-- The real cable copy into the endpoint cells, after the read-only padding test. -/
def hostImage :=
  let host := HostScatter.Layout.fromFrame base initial
  host.prefix initial host.count

/-- The marker-free bundle table and range stores occur after the cable copies. -/
def Inputs.bundleImage := H.bundles.image H.groups (hostImage base initial) H.bundles.cells

/-- Final image includes the common owned-cell count published in frame word 90. -/
def Inputs.image := H.control.published (H.bundleImage base initial)

/-- Numerical and physical input premises of the four native subroutines, using
the actual preceding writer's image at each boundary. -/
structure Ready (w : ℕ) : Prop where
  paddingHeader : Padding.HeaderFits w base initial
  padding : (Padding.Layout.fromFrame base initial).Fits w initial
  host : (HostScatter.Layout.fromFrame base initial).Fits w initial
  frameRoom : base+94 < 2^w
  headerRoom : initial (base+63)+8 < 2^w
  bundleLoaded : H.bundles.loaded base (hostImage base initial)
  bundleFit : H.bundles.Fits w H.sortWidth
  sections : H.bundles.Sections H.groups H.sortWidth (hostImage base initial)
  total : BundleDirectory.«prefix» H.groups H.bundles.cells=H.bundles.bundles
  controlBase : H.control.frame=base
  fields : H.control.Fields (H.bundleImage base initial)
  controls : H.control.Room w

/-- Chronological bound on this suffix, charging the true local widths and group counts. -/
def Inputs.cost :=
  let p := Padding.Layout.fromFrame base initial
  let h := HostScatter.Layout.fromFrame base initial
  p.budget initial + (68+82*h.count+22*h.incident initial +
    (BundleDirectory.setup.slots+16*H.bundles.cells+30*H.bundles.bundles+1 +
      (CellControlRows.setup.slots+H.control.cells*(CellControlRows.body.slots+1)+1+CellControlRows.finish.slots)))

variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {mem : Memory w}

/-- The four actual programs return exactly when the checked padding is valid,
and every successful chronology produces the same computed word image. -/
theorem run (ready : Ready H (pub 0).val (readings mem) w) :
    TestRun pub mac code s mem (H.cost (pub 0).val (readings mem))
      ((Padding.Layout.fromFrame (pub 0).val (readings mem)).Valid (readings mem))
      (fun z => z.mem=H.image (pub 0).val (readings mem)) := by
  let init := readings mem
  let pos := (pub 0).val
  let host := HostScatter.Layout.fromFrame pos init
  let bound := 68+82*host.count+22*host.incident init
  let bundleCost := BundleDirectory.setup.slots+16*H.bundles.cells+30*H.bundles.bundles+1
  let ctlCost := CellControlRows.setup.slots+H.control.cells*(CellControlRows.body.slots+1)+1+CellControlRows.finish.slots
  let write (t : Bank w) (mt : Memory w) (eq : readings mt=H.bundleImage pos init) :
      BoundedRun pub mac CellControlRows.program t mt ctlCost (fun z => z.mem=H.image pos init) := by
    have r := CellControlRows.program_run pub mac t mt H.control ready.controlBase.symm (eq ▸ ready.fields) ready.controls
    exact r.mono le_rfl (fun _ hz => hz.trans (congrArg H.control.published eq))
  have next (t : Bank w) (mt : Memory w) (eq : readings mt=hostImage pos init) :
      BoundedRun pub mac (.seq BundleDirectory.program CellControlRows.program) t mt (bundleCost+ctlCost)
        (fun z => z.mem=H.image pos init) := by
    have r := BundleDirectory.program_runs pub mac t mt H.bundles H.groups (eq ▸ ready.bundleLoaded)
      ready.bundleFit (eq ▸ ready.sections) ready.total
    exact r.seq (fun u mu he => write u mu (he.trans (congrArg (fun x => H.bundles.image H.groups x H.bundles.cells) eq)))
  have cable (t : Bank w) (mt : Memory w) (eq : readings mt=init) :
      BoundedRun pub mac (.seq HostScatter.program (.seq BundleDirectory.program CellControlRows.program)) t mt
        (bound+(bundleCost+ctlCost)) (fun z => z.mem=H.image pos init) := by
    have r := HostScatter.run_fromFrame pub mac t mt (eq ▸ ready.host) ready.frameRoom (eq ▸ ready.headerRoom)
    rw [eq] at r
    exact r.seq (fun u mu he => next u mu he.2.2)
  have pad := Padding.test_verify pub mac s mem pos rfl ready.paddingHeader ready.padding
  apply (pad.seq (fun t mt h => (cable t mt h).asTest (by decide))).mono le_rfl (by simp only [and_true,pos]) (fun _ h => h)

/-- An address outside the actual host-cable intervals, both bundle tables and
both control tables plus the published count survives the entire suffix. -/
theorem image_outside (a : ℕ)
    (cables : let h := HostScatter.Layout.fromFrame base initial
      ∀ i < h.count, ∀ side, h.Owned initial i side → a < h.dest initial i side ∨ h.dest initial i side+h.width initial i ≤ a)
    (ranges : a < H.bundles.ranges ∨ H.bundles.ranges+2*H.bundles.cells ≤ a)
    (rows : a < H.bundles.output ∨ H.bundles.output+6*BundleDirectory.«prefix» H.groups H.bundles.cells ≤ a)
    (ctrl : ¬H.control.outputs a) : H.image base initial a=initial a := by
  have count : a≠H.control.frame+90 := fun eq => ctrl (.inr (.inr eq))
  rw [Inputs.image,CellControlRows.Layout.published,Function.update_of_ne count,CellControlRows.image_outside H.control _ le_rfl ctrl,
    Inputs.bundleImage,H.bundles.image_outside H.groups _ H.bundles.cells a ranges rows]
  exact HostScatter.Layout.prefix_outside _ _ _ _ cables

/-- The four actual output arrays of the bundle and control producers begin
at or above the end of the immutable cube deck. -/
structure AfterDeck (deckEnd : ℕ) : Prop where
  ranges : deckEnd ≤ H.bundles.ranges
  bundles : deckEnd ≤ H.bundles.output
  four : deckEnd ≤ H.control.four
  six : deckEnd ≤ H.control.six

/-- The length-only report and task allocation places these four arrays after
the installed cube deck, for all possible reached local lengths. -/
theorem afterDeck_of_allocation {deckEnd : ℕ} (a : DiagonalTallyAllocation.BeforeTasks)
    (allocated : deckEnd ≤ a.start) (range : H.bundles.ranges=a.ranges) (bundle : H.bundles.output=a.bundleTable)
    (four : H.control.four=a.four) (six : H.control.six=a.six) : AfterDeck H deckEnd := by
  constructor
  all_goals
    simp only [range,bundle,four,six,DiagonalTallyAllocation.BeforeTasks.bundleTable,
    DiagonalTallyAllocation.BeforeTasks.ranges,DiagonalTallyAllocation.BeforeTasks.six,
    DiagonalTallyAllocation.BeforeTasks.four,DiagonalTallyAllocation.BeforeTasks.merged,
    DiagonalTallyAllocation.BeforeTasks.counters,DiagonalTallyAllocation.BeforeTasks.supplement,
    DiagonalTallyAllocation.BeforeTasks.tailWidths]
    omega

variable {F : Type*} [Fintype F] {n b h K d : ℕ}
variable (P : CubePacket.Inputs n b h K d F) (a : CubeArena.Layout) (deckEnd : ℕ)

omit [Fintype F] in
/-- Every genuine returning path of the four-stage suffix preserves the cube's
actual addressed words. The host writes only inside its assigned receiving cells.
The two row producers write above the deck and publish only frame word 90. -/
theorem cube_words (ready : Ready H (pub 0).val (readings mem) w)
    {es t mt} (returned : Runs pub mac code s mem es t mt)
    (low : (pub 0).val+112 ≤ a.header.packetBase) (past : a.stop ≤ deckEnd)
    (location : ∀ x, CubePacket.ReadAt P pub x →
      (∃ j ∈ CubePacket.frameWords, x=(pub 0).val+j) ∨
        (a.header.packetBase ≤ x ∧ x<a.cellBank) ∨ (a.stop ≤ x ∧ x<deckEnd))
    (hostDest : let host := HostScatter.Layout.fromFrame (pub 0).val (readings mem)
      ∀ i < host.count, ∀ side, host.Owned (readings mem) i side →
        a.cellBank ≤ host.dest (readings mem) i side ∧ host.dest (readings mem) i side+host.width (readings mem) i ≤ a.stop)
    (allocated : AfterDeck H deckEnd) : ∀ x, CubePacket.ReadAt P pub x → mt x=mem x := by
  have image : readings mt = H.image (pub 0).val (readings mem) := ((run H ready).sound returned).2
  have first : a.header.packetBase ≤ a.cellBank := by
    have p : a.header.packetBase ≤ a.packetEnd := Nat.le_add_right ..
    have row := a.separated
    have last : a.pairBase ≤ a.cellBank := Nat.le_add_right ..
    omega
  have cellsEnd : a.cellBank ≤ a.stop := Nat.le_add_right ..
  intro x hx
  have marked := location x hx
  have whereAt : (x<a.cellBank ∨ a.stop ≤ x) ∧ x<deckEnd ∧ x ≠ (pub 0).val+90 := by
    rcases marked with ⟨j,hj,rfl⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩
    · simp [CubePacket.frameWords] at hj; omega
    · omega
    · omega
  apply Fin.ext
  change readings mt x = readings mem x
  rw [image]
  apply image_outside H (pub 0).val (readings mem) x
  · dsimp only
    intro i hi side own
    obtain ⟨start,endAt⟩ := hostDest i hi side own
    rcases whereAt.1 with lt|le
    · exact .inl (lt.trans_le start)
    · exact .inr (endAt.trans le)
  · exact .inl (whereAt.2.1.trans_le allocated.ranges)
  · exact .inl (whereAt.2.1.trans_le allocated.bundles)
  · have four := allocated.four
    have six := allocated.six
    have eq := ready.controlBase
    simp only [CellControlRows.Layout.outputs,eq]
    omega

/-- The lookup precondition produced by the genuine owned-group return still
holds after padding, cable scatter, stable bundle compaction and cell controls. -/
theorem preserve (original : CubePacket.Prepared P pub mem) (ready : Ready H (pub 0).val (readings mem) w)
    {es t mt} (returned : Runs pub mac code s mem es t mt)
    (low : (pub 0).val+112 ≤ a.header.packetBase) (past : a.stop ≤ deckEnd)
    (location : ∀ x, CubePacket.ReadAt P pub x →
      (∃ j ∈ CubePacket.frameWords, x=(pub 0).val+j) ∨
        (a.header.packetBase ≤ x ∧ x<a.cellBank) ∨ (a.stop ≤ x ∧ x<deckEnd))
    (hostDest : let host := HostScatter.Layout.fromFrame (pub 0).val (readings mem)
      ∀ i < host.count, ∀ side, host.Owned (readings mem) i side →
        a.cellBank ≤ host.dest (readings mem) i side ∧ host.dest (readings mem) i side+host.width (readings mem) i ≤ a.stop)
    (allocated : AfterDeck H deckEnd) : CubePacket.Prepared P pub mt :=
  original.transfer P (cube_words H P a deckEnd ready returned low past location hostDest allocated)

end FiniteEvaluator.OpenSuffix

end BorderVNP
end Computability
end OAI

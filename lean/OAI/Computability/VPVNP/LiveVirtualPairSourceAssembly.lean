import OAI.Computability.VPVNP.LiveCompressedPairTerminalAssembly
import OAI.Computability.VPVNP.LiveCompressedPairHeaderMemory
import OAI.Computability.VPVNP.LiveCompressedPairStageFrames
import OAI.Computability.VPVNP.LiveVirtualPairOccurrence

/-!
# The source-run certificate of a concrete compressed pair

Use the actual online path and the five terminal blocks to enumerate the
accepted tapes of the fixed eleven-word program. The protected header and
tag follow from the reachable-source frames. Counter readback concerns the
memory of the last vertex block, and the burst bounds concern precisely
the eight startup, online, and five terminal report lists.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM CompressorRecords CompressorRecords.Schedule PairSimulation LocalHistory NetworkKernel
open LiveStageLink PairStages.Group PairStages.Group.CompressedPaths

attribute [local irreducible] stages regs components TerminalProgram.workers

variable {d initial phases : ℕ} {C : Catalog d} {b : Bootstrap} {plan : Online.Config C initial phases}
    {shape : DescriptorSpace.Shape} {limit : ℕ} {segments : VertexImage.Part → VertexImage.Segment}
    {G : PairStages.Group} {B n base : ℕ} {m : Memory G.w}
variable (S : PhysicalStages b plan (terminalBody shape limit segments) G B n base m)

local notation "ports" => publicWords G
local notation "clk" => fuel G
local notation "start" => cursorStartupLogs b ports B n base m initial phases d
local notation "entry" => after m (eventLog start)
local notation "lastStage" => terminalBody shape limit segments

variable {X : Type} (enc : TraceEncoding X) (R : SelectorReindex enc) (visited : X → Memory G.w)
    {Z : Type*} {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {net : Z → Network}
    {scan : (z : Z) → ScanPhase (net z)} {sites : (z : Z) → SiteParsers κ (net z)}
    (descriptor : Z ≃ StagePaths b plan (terminalBody shape limit segments) (publicWords G) (fuel G) Stage.online
      (after m (eventLog (cursorStartupLogs b (publicWords G) B n base m initial phases d))))
    (tags : 32 ≤ 2^G.w) (clock : 26 ≤ clockAt (publicWords G) (fuel G) Stage.terminal)
    (branches : ∀ z : Z, TerminalBranch (G := G) (B := B) (n := n) (base := base) (m := m)
      (b := b) (plan := plan) (shape := shape) (limit := limit) (segments := segments) descriptor (scan z) (sites z) z)
    (emit : (Σ z : Z, TerminalData (scan z) (sites z)) ≃ Set.range R.emit)

/-- Reports of one accepted compressed branch, from cursor startup through the selected online
descriptor to the linked five terminal phases for its actual arc and vertex choices. -/
noncomputable abbrev branchReports (z : Z) (x : TerminalData (scan z) (sites z)) :=
  let t := branches z
  let rows := t.setup.trace (t.bitPaths x.arcs) (t.vertexPaths x.arcs x.choices)
  start ++ (onlineReports (descriptor z) ++
    (TerminalLink.reports (TerminalLink.header ports) rows.logs).map (report ports Stage.terminal))

private theorem range_tapes {J : Type*} (q : J ≃ Raw G m) (bits : List (List Bool)) :
    bits ∈ Set.range (fun x : J => (q x).val) ↔
      ∃ rs, runSegment (native G) clk (some 0) m bits = some rs ∧ endState (some 0) rs = none := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨reports (q x),rawRun _,(q x).property.choose_spec.2.1⟩
  · rintro ⟨rs,run,halt⟩
    let path : Raw G m := ⟨bits,rs,run,halt,trivial⟩
    exact ⟨q.symm path,congrArg Subtype.val (q.apply_symm_apply path)⟩


/-- The canonical descriptor and terminal equivalences, the actual vertex
counter effects and the stage-report budget construct all fields of
`CompressedPaths.SourceRuns`. -/
noncomputable def PhysicalStages.sourceRuns {S₀ H : ℕ}
    (setup : TransferredStartup.Runs (bootstrapRows b initial phases) d (startupLayout b initial phases B n base)
      B n b.degreeBits b.lanesPerBlock b.steps ports (PairTag.address ports) m)
    (baseEq : base = (Layout.pairWorkspace G.constants).eval G.g) (baseFit : base < 2^G.w)
    (shadow : Auxiliary.shadowBase G < 2^G.w)
    (onlineFrame : ∀ a < Auxiliary.tableBase G, S.onlineFrame.word a)
    (terminalFrame : ∀ a < Auxiliary.tableBase G, ∀ p, (S.terminalFrame p).word a)
    (counter : ∀ z (x : TerminalData (scan z) (sites z)) (j : Fin (labelCount G)),
      ((branches z).vertexPaths x.arcs x.choices).val.memory (Auxiliary.counterBase G+j.val) =
        visited (R.decode (emit ⟨z,x⟩)) (Auxiliary.counterBase G+j.val))
    (budget : ∀ z (x : TerminalData (scan z) (sites z)),
      let rs := branchReports descriptor branches z x
      (∀ r ∈ rs, r.events.length+4 ≤ clk) ∧ 4*RAMBuckets.cost Report.probes rs ≤ S₀*H ∧
      ∀ r ∈ rs, 3+r.probes ≤ H) : SourceRuns G m X visited S₀ H := by
  let paths := S.reindexTerminal descriptor tags clock branches emit
  have before : G.addr.val < Auxiliary.tableBase G := by
    rw [(Auxiliary.address_values G shadow).1]
    exact (Auxiliary.geometry_order G).1.trans_le (Auxiliary.geometry_order G).2.1
  have old := tag_before_workspace G.constants G.g
  have upper : Auxiliary.tableBase G ≤ (Layout.oldState G.constants).eval G.g := by
    have table := (Auxiliary.geometry_order G).2.2.1
    change Auxiliary.tableBase G ≤ Auxiliary.counterBase G + G.constants.labels.eval G.g
    omega
  have beforeBase : G.addr.val < base := baseEq ▸ ((before.trans_le upper).trans old)
  refine ⟨enc,R,fun y => (paths y).val,Subtype.val_injective.comp paths.injective,range_tapes paths,
    S.preservesOuterTag shadow beforeBase setup (onlineFrame _ before) (terminalFrame _ before),?_⟩
  intro y rs hr
  obtain ⟨⟨z,x⟩,rfl⟩ := emit.surjective y
  let path := paths (emit ⟨z,x⟩)
  have logs : rs = reports path := Option.some.inj (hr.symm.trans (rawRun path))
  subst rs
  have cap := budget z x
  have actualLogs := S.reindexTerminal_logs descriptor tags clock branches emit z x
  change reports path = branchReports descriptor branches z x at actualLogs
  rw [← actualLogs] at cap
  refine ⟨fun a _ ha => S.headerReadback setup baseEq baseFit a ha (onlineFrame a ha)
    (terminalFrame a ha) (rawRun path) path.property.choose_spec.2.1,?_,cap.2.1,?_⟩
  · intro j
    rw [show after m (eventLog (reports path)) = _ from S.reindexTerminal_after descriptor tags clock branches emit z x]
    exact counter z x j
  · exact fun r hr => ⟨cap.1 r hr,cap.2.2 r hr⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI

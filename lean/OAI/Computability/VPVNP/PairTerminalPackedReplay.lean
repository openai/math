import OAI.Computability.VPVNP.PairTerminalPackedPrefix
import OAI.Computability.VPVNP.PairTerminalPreludeBudget
import OAI.Computability.VPVNP.PairTerminalBootstrapReplay
import OAI.Computability.VPVNP.PairTraversalLowReplay

/-!
# Low words throughout the physical deterministic terminal prefix

The completed calendar supplies the retained inputs for all three native
phases. Their per-report frames include the linked stage changes and the
closing calls, and apply before any shared-bit or site choices are made.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles TerminalPrefix TerminalPrefix.Linked TerminalLink
open scoped Fin.CommRing

variable {w lanes : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "vs" => executeLevels B f hf T hT X z
local notation "ls" => selectedLayers B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "rowsSize" => words B.recordLimit (ls)
local notation "last" => List.length (List.dropLast (ls))

variable (positions baseBits laneBits initialWidth inputN : ℕ) (pub : Fin 11 → Word w)
set_option quotPrecheck false in
local notation "L" => BlockProgram.layout B (pub 2).val positions T
set_option quotPrecheck false in
local notation "tab" => (⟨0,by change 0 < 6; decide⟩ : Fin (L).shape.tables)
local notation "saved" => CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L))
  (CursorRAM.encode w 1) baseBits laneBits (S.degreeExponent 0) initialWidth (incidenceStart L 0)

/-- Every report in the three forced phases preserves words below the live workspace. -/
theorem packed_prefix_frame (data : SelectedPayloadHistory.Data (w := w) B f hf)
    (segments : VertexImage.Part → VertexImage.Segment) (r cap : ℕ) (m phy : Memory w)
    (boundary : ScheduledTrace.Boundary
      (DetailedResident.resident B f hf ⟨leafLayer (siteOrder X), .cursor⟩ L
        (endAddress L) inputN saved data)
      pub (levelWords L : Word w) (directoryRows L) (directoryRows L) (vs) (Y) m)
    (handoff : SourceTransport.Agree ((pub 2).val + 6 ≤ ·) m phy)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ (L).base + 2 ^ r * 2 ^ r)
    (room : (L).base + 2 ^ r * 2 ^ r ≤ 2 ^ w)
    (below : endAddress L + 2 * rowsSize + (Y).totalWidth ≤ TerminalBootstrap.address (L).base r)
    (ordinal : 2 * (tags).length * (X.positions + 1) < 2 ^ w)
    (slots : arcCount (Y) ≤ slotCapacity L) (cells : arcCount (Y) ≤ tableWords L)
    (totalFit : (Y).totalWidth < 2 ^ w)
    (clock₀ : TerminalBootstrap.cost (L).shape B.recordLimit + 1 + 30 ≤ cap) (clock₁ : 60 ≤ cap)
    (clock₂ : TraversalController.callFuel B.recordLimit + 30 ≤ cap)
    (q : QuietPrefix (workers (L).shape B.recordLimit segments) pub cap phy)
    (x : ℕ) (hx : x < (pub 2).val) : ReplayFrame x phy q.reportList := by
  let boot := TerminalBootstrap.report (L).shape B.recordLimit pub 0 phy
  have above : endAddress L ≤ TerminalBootstrap.address (L).base r := by omega
  obtain ⟨⟨history⟩,ready,rs,start,_⟩ := run_boundary B f hf T hT X z positions baseBits laneBits
    initialWidth inputN pub segments r cap m phy (DetailedResident.currentBoundary boundary)
    handoff exp hr reserve room above slots cells totalFit clock₀ clock₁
  let src := prefixMemory pub phy boot rs
  let hdr := TerminalBootstrap.fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab
  have wide : 28 ≤ (L).shape.scalarFields := by change 28 ≤ 54; decide
  have hl : last < (L).levels := by
    rw [TerminalBootstrap.selected_prior_length,BlockProgram.actual_level_count,Nat.mul_comm T]
    omega
  have fields := TraversalResidentHandoff.fields_of_start L last hl tab hdr B.recordLimit r (Y)
    pub phy src ready exp hr reserve room above wide cells rs start start.handoff_rows.1
  have retained := TraversalResidentHandoff.selected_resident B f hf T hT X z
    L baseBits laneBits tab history fields hl wide
  let ds := retained.choose
  have stored := retained.choose_spec.2.1
  have heads := retained.choose_spec.2.2
  have head := q.force_start start clock₀ clock₁
  have e : q.prefixRows.val.memory = src := head.2.2.2
  have xbase : x < endAddress L := by
    have first : (L).base ≤ endAddress L := by
      simp only [endAddress,levelStart,levelsBase,directoryBase,plannerTag,frameBase]
      omega
    exact hx.trans_le first
  have cand : Phase _ pub cap (.resume Stage.traversalRows 0) src
      q.traversalRows.val.choices q.traversalRows.val.logs q.traversalRows.val.memory :=
    (congrArg (fun m' => Phase _ pub cap (.resume Stage.traversalRows 0) m'
      q.traversalRows.val.choices q.traversalRows.val.logs q.traversalRows.val.memory) e).mp
        q.traversalRows.prop
  have third := TraversalController.selected_linked_low_replay B f hf T hT X z
    (endAddress L) src ds pub (Y).totalWidth (TerminalBootstrap.address (L).base r)
    (levelStart L 0) (levelWords L) stored heads below ordinal
    (workers (L).shape B.recordLimit segments) cap rfl clock₂ cand x xbase
  apply q.replayFrame_packedStart L ⟨last,hl⟩ tab hdr B.recordLimit r cap (Y) phy rs
    ready exp hr reserve room above slots start clock₀ clock₁ x hx
  exact (congrArg (fun m' => ReplayFrame x m'
    (reports (header pub) q.traversalRows.val.logs)) e).mpr third

end PairSimulation.TerminalProgram

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles TerminalPrefix TerminalLink CursorBounds CursorNetwork Filter
open LiveProgram.PairStages.Group.CompressedPaths (publicWords fuel)
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

set_option exponentiation.threshold 10000 in
/-- A common length threshold gives the entire chronological low-word frame
for each selected descriptor path on the fixed live worker bank. -/
theorem eventually_packed_prefix_frame (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hstart : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : LiveProgram.PairStages.Group)
      (_ : G.w = wordBits b n) (_ : ((publicWords G) 2).val = start n)
      (_ : ((publicWords G) 7).val = addressBits b n) (_ : n ^ 10000 ≤ G.clock)
      {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let L := BlockProgram.layout B ((publicWords G) 2).val X.positions T
      let E := B.execute f hf T hT X
      let cap := LiveProgram.CompressedPair.clockAt (publicWords G) (fuel G)
        LiveProgram.CompressedPair.Stage.terminal
      ∀ (z : E.Choices) (baseBits laneBits initialWidth inputN : ℕ)
        (data : SelectedPayloadHistory.Data (w := G.w) B f hf)
        (segments : VertexImage.Part → VertexImage.Segment) (m phy : Memory G.w),
        let saved := CursorRAM.ScheduleInit.inputs (CursorRAM.encode G.w (directoryBase L))
          (CursorRAM.encode G.w 1) baseBits laneBits (S.degreeExponent 0) initialWidth
          (incidenceStart L 0)
        ScheduledTrace.Boundary
            (DetailedResident.resident B f hf ⟨leafLayer (siteOrder X), .cursor⟩ L
              (endAddress L) inputN saved data)
            (publicWords G) (levelWords L : Word G.w) (directoryRows L) (directoryRows L)
            (executeLevels B f hf T hT X z) (E.finalState z) m →
        SourceTransport.Agree (((publicWords G) 2).val + 6 ≤ ·) m phy →
        ∀ q : QuietPrefix (workers (BlockProgram.allocationShape B) B.recordLimit segments)
            (publicWords G) cap phy,
          ∀ x < ((publicWords G) 2).val, ReplayFrame x phy q.reportList := by
  filter_upwards [TerminalLayout.eventually_preludeRoom B u b hb hstart] with n fit
  intro G hw baseWord exp clock base lanes labels hD hT A _ f hf X T L E cap z baseBits laneBits
    initialWidth inputN data segments m phy saved boundary handoff
  have geometry := fit labels hD hT A f hf z G clock
  dsimp only at geometry
  rw [← baseWord,← hw] at geometry
  obtain ⟨hr,reserve,room,below,ordinal,slots,cells,totalFit,clock₀,clock₁,clock₂⟩ := geometry
  have bank := TerminalLayout.packed_workers B ((publicWords G) 2).val X.positions T segments
  change ∀ q : QuietPrefix (workers (BlockProgram.allocationShape B) B.recordLimit segments)
    (publicWords G) cap phy, ∀ x < ((publicWords G) 2).val, ReplayFrame x phy q.reportList
  rw [← bank]
  exact packed_prefix_frame B f hf T hT X z X.positions baseBits laneBits initialWidth inputN
    (publicWords G) data segments (addressBits b n) cap m phy boundary handoff exp hr reserve
    room below ordinal slots cells totalFit clock₀ clock₁ clock₂

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI

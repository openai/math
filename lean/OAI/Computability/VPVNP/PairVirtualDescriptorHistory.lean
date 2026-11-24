import OAI.Computability.VPVNP.LiveVirtualPairPaperDescriptor
import OAI.Computability.VPVNP.PairTerminalCalendarBoundary
import OAI.Computability.VPVNP.PairShrinkSiteHistory
import OAI.Computability.VPVNP.LiveCompressedPairStartupInputs
import OAI.Computability.VPVNP.FixedProgramOperandFits

/-! # Recovering the selected parser records from the actual online stage -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open Compression CursorBounds CursorNetwork BurstRAM LiveProgram CompressedPair
open PairStages.Group.CompressedPaths CompressorRecords ScheduledTrace DescriptorSpace
open PairSimulation LocalHistory TraversalRows TraversalRoles
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {u : PairExponents B.growthConstant}
    {D : FixedProgramDiagonal.Program} {C n : ℕ} {hn : 2 ≤ n} {V : D.VirtualPairs B u hn C}
    {A : Type*} [CommRing A] {f : B.Entry → A} {ok : B.IsSolution f}
    {c : Constants} {labels : c.motifLabels = Fintype.card B.Entry} {base clk rate : ℕ}
    {pub : Fin 11 → Word (wordBits D.addressFactor n)} {m : Memory (wordBits D.addressFactor n)}
    (desc : V.PaperDescriptor f ok c labels base clk rate pub m)
    (z : (B.execute f ok (blockCount (u.θ : ℝ) n) le_rfl V.scanState).Choices)

local notation "T₀" => blockCount (u.θ : ℝ) n
local notation "X₀" => VirtualPairs.scanState V
local notation "w₀" => wordBits D.addressFactor n
local notation "pos₀" => State.positions (X₀)
local notation "L₀" => BlockProgram.layout B (Fin.val (pub 2)) (pos₀) (T₀)
local notation "data₀" => CompiledResident.payload (w := w₀) B f ok (pub 2) (pos₀) (T₀) n
local notation "passes₀" => executeLevels B f ok (T₀) le_rfl (X₀) z

/-- The detailed descriptor result contains the payload of every selected
pass, with exactly the workspace word used by the physical pair program. -/
theorem VirtualPairs.PaperDescriptor.past_online (workspace : (pub 2).val = base) :
    SelectedPayloadHistory.Past B f ok (L₀) (data₀) (passes₀) (desc.result.trace.cut.part z).memory := by
  have positions : (X₀).positions = initialPositions D.addressFactor n := by
    rw [V.scanState_pairInput]
    exact pairInput_positions S _ _
  have word : (base : Word w₀) = pub 2 := workspace ▸ Fin.cast_val_eq_self _
  have h := DetailedResident.payloads (desc.result.final z).stored
  rw [positions,workspace,←word]
  exact h

/-- The sole write at the online-to-terminal handoff changes the scheduler
tag. Every recorded graph, term and argument field is above this address. -/
theorem VirtualPairs.PaperDescriptor.past_calendar (workspace : (pub 2).val = base)
    (tag : (PairTag.address pub).val < (pub 2).val+6) :
    SelectedPayloadHistory.Past B f ok (L₀) (data₀) (passes₀) (onlinePost (desc.paths z)) := by
  have handoff := TerminalPrefix.Linked.handoff_of_transfer pub (desc.post z) tag
  apply (desc.past_online z workspace).transfer
  intro x lo _
  have start : (pub 2).val+6 ≤ levelsBase (L₀) := by
    unfold levelsBase directoryBase plannerTag frameBase
    change (pub 2).val+6 ≤ (pub 2).val+9+_+1+_
    omega
  exact (handoff x (start.trans lo)).symm

/-- The graph part of that same postcondition supplies the terminal
bootstrap's actual online boundary. -/
theorem VirtualPairs.PaperDescriptor.current_at_online (workspace : (pub 2).val = base) :
    let b := virtualBits D.addressFactor n - reservedLanes B u n
    let lanes := reservedLanes B u n
    let frame := cursorFrame (L₀) (S.degreeExponent 0) b lanes (initialWidth D.addressFactor n)
    let current := CurrentResident.resident B f ok ⟨leafLayer (siteOrder (X₀)),.cursor⟩ (L₀) (endAddress (L₀)) n frame
    Boundary current pub (levelWords (L₀) : Word w₀) (directoryRows (L₀)) (directoryRows (L₀))
      (passes₀) ((B.execute f ok T₀ le_rfl (X₀)).finalState z) (desc.result.trace.cut.part z).memory := by
  have positions : (X₀).positions = initialPositions D.addressFactor n := by
    rw [V.scanState_pairInput]; exact pairInput_positions S _ _
  intro b lanes frame current
  change Boundary (CurrentResident.resident B f ok _ (L₀) _ n _) _ _ _ _ _ _ _
  dsimp only [frame]
  rw [positions,workspace]
  exact DetailedResident.currentBoundary (desc.result.final z)

section Site

open PairStages.Group.Auxiliary

variable {ht : 21 ≤ 2^(D.geometry n).w} {dispatch : 44 ≤ n^10000}
local notation "G₀" => D.executionGroup n ht dispatch
local notation "Y₀" => StateExecution.finalState (B.execute f ok (T₀) le_rfl (X₀)) z

/-- Every later site can still retrieve those selected shrink and refresh
rows after the shared-bit scan and preceding histogram flushes. -/
theorem VirtualPairs.PaperDescriptor.past_site (workspace : (pub 2).val = base)
    (tag : (PairTag.address pub).val < (pub 2).val+6)
    (actual : pub = terminalOperands G₀) {tab : Fin (L₀).shape.tables} {baseBits laneBits j : ℕ}
    {bits : Fin (Y₀).totalWidth → Bool} {reference site : Memory w₀}
    (entry : TerminalProgram.VertexEntry B f ok T₀ le_rfl (X₀) z (L₀) tab baseBits laneBits pub
      (onlinePost (desc.paths z)) reference bits)
    (fit : VertexPacked G₀ (L₀) B.recordLimit (selected B f ok T₀ le_rfl (X₀) z) (Y₀).totalWidth)
    (later : LinkedVertexMemory G₀ reference j site) :
    SelectedPayloadHistory.Past B f ok (L₀) (data₀) (passes₀) site := by
  subst pub
  exact entry.packedSitePayload fit later (desc.past_calendar z workspace tag)

end Site

open Filter

/-- The actual group workspace and online tag bounds hold before choosing
any program parameters or selected path at the given length. -/
theorem eventually_descriptor_history (D : FixedProgramDiagonal.Program) (B : S.Templates)
    (u : PairExponents B.growthConstant) (C : ℕ) (hnum : D.numerator = (liveRatio u).num)
    (hden : D.denominator = (liveRatio u).den) (labels : D.constants.motifLabels = Fintype.card B.Entry) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C)
      (ht : 21 ≤ 2^(D.geometry n).w) (hc : 44 ≤ n^10000) (A : Type*) [CommRing A]
      (f : B.Entry → A) (ok : B.IsSolution f) (rate : ℕ) (m : Memory (D.geometry n).w),
      let G := D.executionGroup n ht hc
      let pub := publicWords G
      let base := (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
      let T := blockCount (u.θ : ℝ) n
      let X := V.scanState
      let L := BlockProgram.layout B (pub 2).val X.positions T
      let data := CompiledResident.payload B f ok (pub 2) X.positions T n
      ∀ desc : V.PaperDescriptor f ok D.constants labels base (fuel G) rate pub m,
      ∀ z : (B.execute f ok T le_rfl X).Choices,
        SelectedPayloadHistory.Past B f ok L data (executeLevels B f ok T le_rfl X z) (onlinePost (desc.paths z)) := by
  filter_upwards [eventually_startup_inputs D.constants D.address_pos (liveCapacity_polynomial u)] with n valid
  intro hn V ht hc A _ f ok rate m G pub base T X L data desc z
  have geometry := paperGeometry_eq D B u hnum hden n
  obtain ⟨space,_,_,tag⟩ := valid G.lit
  rw [← geometry] at space tag
  change (pub 2).val = base at space
  change (PairTag.address pub).val < (pub 2).val at tag
  exact desc.past_calendar z space (tag.trans_le (Nat.le_add_right _ _))

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI

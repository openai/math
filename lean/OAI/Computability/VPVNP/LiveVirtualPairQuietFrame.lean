import OAI.Computability.VPVNP.LiveVirtualPairPreludeCharge
import OAI.Computability.VPVNP.PairTerminalPackedReplay

/-! # Preserving every low address on the actual terminal setup reports -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorBounds CursorNetwork BurstRAM LiveProgram CompressedPair
open PairStages.Group.CompressedPaths LabelEvaluator CompressorRecords ScheduledTrace DescriptorSpace
open PairSimulation LocalHistory TerminalLink TraversalRows TraversalRoles TerminalPrefix Filter
open scoped Fin.CommRing
set_option quotPrecheck false

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {u : PairExponents B.growthConstant}
  {D : FixedProgramDiagonal.Program} {C n : ℕ} {hn : 2 ≤ n} {V : D.VirtualPairs B u hn C}
  {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
  {c : Constants} {labels : c.motifLabels = Fintype.card B.Entry}
  {base clk rate : ℕ} {pub : Fin 11 → Word (wordBits D.addressFactor n)} {m : Memory (wordBits D.addressFactor n)}

local notation "ww" => wordBits D.addressFactor n
local notation "T" => blockCount (u.θ : ℝ) n
local notation "P" => initialPositions D.addressFactor n
local notation "lanes₀" => reservedLanes B u n
local notation "base₀" => virtualBits D.addressFactor n-reservedLanes B u n
local notation "E" => B.execute f hf T le_rfl V.scanState
local notation "L" => BlockProgram.layout B base P T
local notation "tab" => (⟨0, by change 0 < 6; decide⟩ : Fin (L).shape.tables)
local notation "parts" => paperSegments B u c labels
local notation "bank₀" => TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit parts
local notation "termClock" => clockAt pub clk CompressedPair.Stage.terminal
local notation "payload₀" => CompiledResident.payload (w := ww) B f hf (base : Word ww) P T n

/-- Every intermediate report of the quiet prefix preserves each cell
below the workspace. This applies on the runtime bank and the equal fixed
bank used by the vertex interpreter. -/
private theorem frame_of_room
    (desc : V.PaperDescriptor f hf c labels base clk rate pub m)
    (z : (E).Choices) :
    let r := addressBits D.addressFactor n
    let Y := (E).finalState z
    let ls := selectedLayers B f hf T le_rfl V.scanState z
    let tags := selected B f hf T le_rfl V.scanState z
    let phy := onlinePost (desc.paths z)
    let Safe (W : TerminalLink.Stage → PairTable) :=
      ∀ q : QuietPrefix W pub termClock phy, ∀ x < (pub 2).val, ReplayFrame x phy q.reportList
    TerminalLayout.PreludeRoom pub L r termClock B.recordLimit V.scanState.positions
      (words B.recordLimit ls) tags.length Y.totalWidth (arcCount Y) →
      Safe (TerminalProgram.workers (L).shape B.recordLimit parts) ∧ Safe bank₀ := by
  intro r Y ls tags phy Safe h
  have baseWord : (pub 2).val = base := h.workspace
  subst base
  let payload := CompiledResident.payload (w := ww) B f hf ((pub 2).val : Word ww) P T n
  have handoff := Linked.handoff_of_transfer pub (desc.post z) h.tag
  have raw : Safe (TerminalProgram.workers (BlockProgram.layout B (pub 2).val P T).shape B.recordLimit parts) :=
    TerminalProgram.packed_prefix_frame B f hf T le_rfl V.scanState z P base₀ lanes₀
      (initialWidth D.addressFactor n) n pub payload parts r termClock (desc.result.trace.cut.part z).memory phy
      (desc.result.final z) handoff h.exponent h.exponentFit h.reserve h.room h.below h.ordinal h.slots h.cells
      h.totalFit h.bootClock h.widthClock h.rowClock
  exact ⟨raw,(congrArg Safe (TerminalLayout.packed_workers B (pub 2).val P T parts)).mp raw⟩

set_option exponentiation.threshold 10000 in
theorem eventually_paperDescriptorQuietFrame (D : FixedProgramDiagonal.Program) (B : S.Templates)
    (u : PairExponents B.growthConstant) (C : ℕ) (hb : max S.laneBits 5 ≤ D.addressFactor)
    (num : D.numerator = (liveRatio u).num) (den : D.denominator = (liveRatio u).den)
    (c : Constants) (labels : c.motifLabels = Fintype.card B.Entry) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (V : D.VirtualPairs B u hn C)
      (ht : 21 ≤ 2^(D.geometry n).w) (hc : 44 ≤ n^10000) {p : Nat.Primes}
      (M : Model p (B.compressorDegree n) (B.compressorEquations hn C)),
      let G := D.executionGroup n ht hc
      let pub := publicWords G
      let clk := fuel G
      let base := (LiveProgram.Layout.pairWorkspace D.constants).eval (D.geometry n)
      let alloc := BlockProgram.layout B base (initialPositions D.addressFactor n) (blockCount (u.θ : ℝ) n)
      let bank (shape : DescriptorSpace.Shape) := TerminalProgram.workers shape B.recordLimit (paperSegments B u c labels)
      ∀ (rate : ℕ) (m : Memory (wordBits D.addressFactor n))
        (desc : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M)
          c labels base clk rate pub m) (z : (V.selection (M := M)).Choices),
        let phy := onlinePost (desc.paths z)
        let Safe (W : TerminalLink.Stage → PairTable) :=
          ∀ q : QuietPrefix W pub (clockAt pub clk CompressedPair.Stage.terminal) phy,
            ∀ x < (pub 2).val, ReplayFrame x phy q.reportList
        Safe (bank alloc.shape) ∧ Safe (bank (BlockProgram.allocationShape B)) := by
  filter_upwards [eventually_paperDescriptorRoom D B u C hb num den] with n room
  intro hn V ht hc p M G pub clk base alloc bank rate m desc z
  exact frame_of_room desc z (room hn V ht hc M z)

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI

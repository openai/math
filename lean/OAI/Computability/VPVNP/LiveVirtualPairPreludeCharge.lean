import OAI.Computability.VPVNP.PairTerminalSelectedStartCharges
import OAI.Computability.VPVNP.LiveVirtualPairPaperDescriptor
import OAI.Computability.VPVNP.LiveVirtualPairPreludeRoom

/-! # Forced terminal charges on the selected finite-model descriptor -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace FixedProgramDiagonal.Program

open Compression CursorBounds CursorNetwork BurstRAM LiveProgram CompressedPair
open PairStages.Group.CompressedPaths LabelEvaluator CompressorRecords ScheduledTrace DescriptorSpace
open PairSimulation LocalHistory TerminalLink TraversalRows TraversalRoles TerminalPrefix Filter
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {u : PairExponents B.growthConstant}
  {D : FixedProgramDiagonal.Program} {C n : ℕ} {hn : 2 ≤ n} (V : D.VirtualPairs B u hn C)
  {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
  {c : Constants} {labels : c.motifLabels = Fintype.card B.Entry}
  {base clk rate : ℕ} {pub : Fin 11 → Word (wordBits D.addressFactor n)} {m : Memory (wordBits D.addressFactor n)}

local notation "addr" => D.addressFactor
local notation "ww" => wordBits D.addressFactor n
local notation "T" => blockCount (u.θ : ℝ) n
local notation "P" => initialPositions D.addressFactor n
local notation "l" => reservedLanes B u n
local notation "baseBits" => virtualBits D.addressFactor n - reservedLanes B u n
local notation "E" => B.execute f hf T le_rfl V.scanState
local notation "L" => BlockProgram.layout B base P T
local notation "bound" => TerminalBootstrap.cost (BlockProgram.allocationShape B) B.recordLimit + 1
local notation "parts" => paperSegments B u c labels
local notation "termClock" => clockAt pub clk CompressedPair.Stage.terminal

attribute [local irreducible] BlockProgram.script CursorNetwork.cursorState TerminalProgram.workers
  CompressedPair.stages CompressedPair.regs

/-- Extract the full terminal prelude charge from the compiled payload and
the physical RAM at the exit of this descriptor. -/
private theorem prelude_of_room
    (desc : V.PaperDescriptor f hf c labels base clk rate pub m)
    (z : (E).Choices) (trace : FiveTrace (TerminalProgram.workers (L).shape B.recordLimit parts)
      pub termClock (onlinePost (desc.paths z)))
    (baseWord : (pub 2).val = base) (tag : (PairTag.address pub).val < (pub 2).val+6)
    (exp : (pub 7).val = addressBits addr n) :
    let r := addressBits addr n
    let Y := (E).finalState z
    let ls := selectedLayers B f hf T le_rfl V.scanState z
    let tags := selected B f hf T le_rfl V.scanState z
    r < ww → 32 ≤ (L).base+2^r*2^r → (L).base+2^r*2^r ≤ 2^ww →
    endAddress L + 2*words B.recordLimit ls + Y.totalWidth ≤ TerminalBootstrap.address (L).base r →
    2*tags.length*(V.scanState.positions+1) < 2^ww →
    arcCount Y ≤ slotCapacity L → arcCount Y ≤ tableWords L → Y.totalWidth < 2^ww →
    TerminalBootstrap.cost (L).shape B.recordLimit+1+30 ≤ termClock → 60 ≤ termClock →
    TraversalController.callFuel B.recordLimit+30 ≤ termClock →
      Nonempty (PreludeCosts V.scanState Y pub trace S.steps B.recordLimit T bound) := by
  subst base
  intro r Y ls tags hr reserve room below ord slots cells totalFit clock₀ clock₁ clock₂
  let payload := CompiledResident.payload (w := ww) B f hf ((pub 2).val : Word ww) P T n
  have handoff := Linked.handoff_of_transfer pub (desc.post z) tag
  exact TerminalProgram.packed_prefix_costs B f hf T le_rfl V.scanState z P (baseBits) l (initialWidth addr n) n pub
    payload parts r termClock (desc.result.trace.cut.part z).memory (onlinePost (desc.paths z))
    (desc.result.final z) handoff exp hr reserve room below ord slots cells totalFit clock₀ clock₁ clock₂ trace

set_option exponentiation.threshold 10000 in
/-- The actual finite model, source calendar, and accepted terminal trace all
come after the length threshold. The bootstrap bound is the one charged by
the fixed branch clock. -/
theorem eventually_paperDescriptorPrelude (D : FixedProgramDiagonal.Program) (B : S.Templates)
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
      let bank := TerminalProgram.workers alloc.shape B.recordLimit (paperSegments B u c labels)
      ∀ (rate : ℕ) (m : Memory (wordBits D.addressFactor n))
        (desc : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M)
          c labels base clk rate pub m) (z : (V.selection (M := M)).Choices)
        (trace : FiveTrace bank pub (clockAt pub clk CompressedPair.Stage.terminal) (onlinePost (desc.paths z))),
        Nonempty (PreludeCosts V.scanState ((V.selection (M := M)).finalState z) pub trace S.steps B.recordLimit
          (blockCount (u.θ : ℝ) n) (TerminalBootstrap.cost (BlockProgram.allocationShape B) B.recordLimit+1)) := by
  filter_upwards [eventually_paperDescriptorRoom D B u C hb num den] with n room
  intro hn V ht hc p M G pub clk base alloc bank rate m desc z trace
  have h := room hn V ht hc M z
  exact prelude_of_room V desc z trace h.workspace h.tag h.exponent h.exponentFit h.reserve h.room h.below
    h.ordinal h.slots h.cells h.totalFit h.bootClock h.widthClock h.rowClock

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI

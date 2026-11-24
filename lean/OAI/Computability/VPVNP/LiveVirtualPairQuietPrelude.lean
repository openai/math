import OAI.Computability.VPVNP.LiveVirtualPairPreludeCharge
import OAI.Computability.VPVNP.PairTerminalQuietHandoff
import OAI.Computability.VPVNP.PairTerminalPreludeUnique

/-! # Native terminal entry from the selected finite-model descriptor -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace PairSimulation.TerminalLink

open BurstRAM LiveProgram

/-- The physical data exposed to the shared-bit and site interpreters by
a deterministic prefix. Vertex readback is available on any fourth block
with the indicated tape. -/
structure QuietData {w cap : ℕ} {workers : Stage → PairTable} {pub : Fin 11 → Word w}
    {input : Memory w} (q : QuietPrefix workers pub cap input)
    (lo width prefixCount traversalCount : ℕ) (post : (Fin width → Bool) → Memory w → Prop) : Prop where
  boot : q.boot.val.choices = [[]]
  prefixRows : q.prefixRows.val.choices = List.replicate prefixCount []
  traversal : q.traversalRows.val.choices = List.replicate traversalCount []
  layout : FinalBits.Worker.Layout pub q.traversalRows.val.memory lo width
  valid : (Entry.resume Stage.sharedBits (0 : Word w)).Valid (header pub) q.traversalRows.val.memory
  clock : 54 ≤ cap
  headerFit : (header pub).val+32 ≤ 2^w
  low : (pub 2).val ≤ lo
  below : lo+width ≤ (header pub).val
  entry : ∀ bits (p : q.BitPaths), p.val.choices = FinalBits.calls bits ++ [[]] → post bits p.val.memory

end PairSimulation.TerminalLink

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

/-- The checked vertex data, DFS history, wires and archived payloads on the
same post-memory that the selected descriptor gives to the terminal program. -/
abbrev VirtualPairs.PaperDescriptor.QuietData
    (desc : V.PaperDescriptor f hf c labels base clk rate pub m) (z : (E).Choices)
    (q : QuietPrefix bank₀ pub termClock (onlinePost (desc.paths z))) : Prop :=
  let Y := (E).finalState z
  let ls := selectedLayers B f hf T le_rfl V.scanState z
  let tags := selected B f hf T le_rfl V.scanState z
  TerminalLink.QuietData q (endAddress L+words B.recordLimit ls) Y.totalWidth (arcCount Y+1)
    (2*(ls.map Layer.count).sum+2*tags.length+1) fun bits memory =>
      TerminalProgram.VertexEntry B f hf T le_rfl V.scanState z L tab base₀ lanes₀ pub
          (onlinePost (desc.paths z)) memory bits ∧
        SelectedPayloadHistory.Past B f hf L payload₀ (executeLevels B f hf T le_rfl V.scanState z) memory

private theorem quiet_of_room
    (desc : V.PaperDescriptor f hf c labels base clk rate pub m)
    (z : (E).Choices) (baseWord : (pub 2).val = base)
    (tag : (PairTag.address pub).val < (pub 2).val+6) (exp : (pub 7).val = addressBits D.addressFactor n) :
    let r := addressBits D.addressFactor n
    let Y := (E).finalState z
    let ls := selectedLayers B f hf T le_rfl V.scanState z
    let tags := selected B f hf T le_rfl V.scanState z
    r < ww → 32 ≤ (L).base+2^r*2^r → (L).base+2^r*2^r ≤ 2^ww →
    endAddress L + 2*words B.recordLimit ls + Y.totalWidth ≤ TerminalBootstrap.address (L).base r →
    2*tags.length*(V.scanState.positions+1) < 2^ww →
    arcCount Y ≤ slotCapacity L → arcCount Y ≤ tableWords L → Y.totalWidth < 2^ww →
    TerminalBootstrap.cost (L).shape B.recordLimit+1+30 ≤ termClock → 60 ≤ termClock →
    TraversalController.callFuel B.recordLimit+30 ≤ termClock →
      ∃ q, desc.QuietData z q := by
  subst base
  intro r Y ls tags hr reserve room below ord slots cells totalFit clock₀ clock₁ clock₂
  let alloc := BlockProgram.layout B (pub 2).val P T
  let payload := CompiledResident.payload (w := ww) B f hf ((pub 2).val : Word ww) P T n
  let phy := onlinePost (desc.paths z)
  let rowWords := words B.recordLimit ls
  let wireBase := endAddress alloc+rowWords
  let post (bits : Fin Y.totalWidth → Bool) (mem : Memory ww) : Prop :=
    TerminalProgram.VertexEntry B f hf T le_rfl V.scanState z alloc
      (⟨0, by change 0 < 6; decide⟩ : Fin alloc.shape.tables) base₀ lanes₀ pub phy mem bits ∧
    SelectedPayloadHistory.Past B f hf alloc payload (executeLevels B f hf T le_rfl V.scanState z) mem
  let Good (W : TerminalLink.Stage → PairTable) : Prop :=
    ∃ q : QuietPrefix W pub termClock phy, TerminalLink.QuietData q wireBase Y.totalWidth
      (arcCount Y+1) (2*(ls.map Layer.count).sum+2*tags.length+1) post
  change Good bank₀
  apply (congrArg Good (TerminalLayout.packed_workers B (pub 2).val P T parts)).mp
  have handoff := Linked.handoff_of_transfer pub (desc.post z) tag
  obtain ⟨q,paths,boot,pref,rows,layout,each⟩ :=
    TerminalProgram.packed_detailed_prefix B f hf T le_rfl V.scanState z P base₀ lanes₀
      (initialWidth D.addressFactor n) n pub payload parts r termClock (desc.result.trace.cut.part z).memory phy
      (desc.result.final z) handoff exp hr reserve room below ord slots cells totalFit clock₀ clock₁ clock₂
  have head : (header pub).val = TerminalBootstrap.address alloc.base r :=
    TerminalPrefix.header_val alloc pub r rfl exp hr reserve room
  have lower : (pub 2).val ≤ endAddress alloc := by
    apply le_trans _ (directoryBase_le_end alloc)
    dsimp only [directoryBase,plannerTag,frameBase]
    change (pub 2).val ≤ (pub 2).val+9+(_+1)+1; omega
  have hHeader : (header pub).val+32 ≤ 2^ww := by
    rw [head,TerminalBootstrap.address]
    change 32 ≤ alloc.base+_ at reserve
    change alloc.base+_ ≤ 2^ww at room
    omega
  have hWire : wireBase+Y.totalWidth ≤ (header pub).val := by
    rw [head]
    change endAddress alloc+2*rowWords+Y.totalWidth ≤ TerminalBootstrap.address alloc.base r at below
    change endAddress alloc+rowWords+Y.totalWidth ≤ _
    omega
  refine ⟨q,boot,pref,rows,layout,q.valid_sharedBits (reserve.trans room),
    (by omega : 54 ≤ termClock),hHeader,lower.trans (Nat.le_add_right ..),hWire,?_⟩
  intro bits p tape
  have eqn : p = paths bits := CompletedPhase.eq_of_choices _ _ (tape.trans (each bits).1.symm)
  exact eqn ▸ (each bits).2

set_option exponentiation.threshold 10000 in
/-- Uniform selection of the actual fixed-bank prefix at the physical
descriptor post-memory. Its vertex readback holds on each shared-bit path
chosen by the canonical nomination. -/
theorem eventually_paperDescriptorQuiet (D : FixedProgramDiagonal.Program) (B : S.Templates)
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
      ∀ (rate : ℕ) (m : Memory (wordBits D.addressFactor n))
        (desc : V.PaperDescriptor (B.compressorValues hn M) (B.compressorValues_solution hn M)
          c labels base clk rate pub m) (z : (V.selection (M := M)).Choices),
        ∃ q, desc.QuietData z q := by
  filter_upwards [eventually_paperDescriptorRoom D B u C hb num den] with n room
  intro hn V ht hc p M G pub clk base rate m desc z
  have h := room hn V ht hc M z
  exact quiet_of_room desc z h.workspace h.tag h.exponent h.exponentFit h.reserve h.room h.below h.ordinal
    h.slots h.cells h.totalFit h.bootClock h.widthClock h.rowClock

end FixedProgramDiagonal.Program

end

end VPVNP
end Computability
end OAI

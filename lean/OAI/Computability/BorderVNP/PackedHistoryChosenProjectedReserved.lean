import OAI.Computability.BorderVNP.PackedHistoryChosenReservedGeometry
import OAI.Computability.BorderVNP.PackedHistoryNormalizedRAM
import OAI.Computability.BorderVNP.PackedHistoryProjectedProfile

/-! # Decoding the augmented public program on an arbitrary shared-header exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput DiagonalResidueRAM
open VPVNP BurstRAM RAMTape TeamContraction TeamContraction.ProcessorSlots VerifierNetwork
open RoutingISA RoutingISA.Pins GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit
open Shortening Adaptive Packing Epoch.Round RoutingISA.Evaluator
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter PublicCapacity
open private PinClear.read from OAI.Computability.BorderVNP.PackedHistoryPreparedInput
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {K : Type*} [Field K] {dim labels : ℕ} {ι : Type} [Fintype ι]
variable {paid : PaidIdentity K dim labels} {aux : ι → K} {q k s : ℕ}
variable {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField paid aux q k s ord}
variable {chart : AdvisedBranch R} [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
variable {teams r multBits tally W pinWidth pc reg routines a link n e : ℕ}
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth
variable (reader : ChosenReader chart (teams+1) r multBits tally W pinWidth)
variable (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc reg 32 routines)
variable (S : SiteData teams r reg 32 W a) (fit : fitsWith physical reg 32 r W a teams link n e)
variable (valuation entry totals : Fin (teams+1) → ℕ) (old : Fin (teams+1) → Fin 81 → Word W)
variable (L : Routing.WireLayout (teams+1) r link)
variable [NeZero dim] {sched : Normalized.SiteSchedule paid} {level rounds : ℕ}
    {PortName X : Type} [Fintype PortName] [Fintype X] {bits : PortName → ℕ} {shape : ℕ → Shape}
    {PinsW : ℕ → Type} [∀ j, Fintype (PinsW j)] {deep : sched.floor+1+sched.drop*rounds ≤ level}
    {good : ∀ j, EnrichedOuter.State sched level PortName bits shape PinsW j → Prop}
    {InnerW : ℕ → ℕ → Type} [∀ j i, Fintype (InnerW j i)] {ww : ℕ → ℕ → ℕ}
    (M : EnrichedOuter.Machine deep good InnerW ww)
    (leaf : Admissible good 0) (bottom : Frame X (PinsW 0)) (x : X → Bool) (input : bottom.eval x = leaf.val.words)
    {reserve o b : ℕ} (widths : ℕ → ℕ) (order : ∀ j, EnrichedOuter.Machine.Guess sched level ww j ≃ Fin (widths j))
    (fits : broadcastWidth (fan sched) widths rounds ≤ reserve)
    {A : ℕ → Type} [∀ j, Fintype (A j)] (pick : ∀ j, PinsW j → A j)
    (aug : Steps (fan sched) rounds A (EnrichedOuter.Machine.Guess sched level ww))
    (project : StepsProject pick aug M.steps)
    (front : Frame X (A 0)) (front_eq : front.eval x ∘ pick 0 = bottom.eval x)
    (emit : Frame ((X ⊕ Fin reserve) ⊕ A rounds) (Fin o × Fin b))
variable (D : Packing.Directory.Layout)
local notation "history" => PackedHistoryCircuit.compile aug rounds le_rfl (repeatLeaf (fan sched) front rounds)
local notation "slots" => broadcastOrder (fan sched) widths order rounds
local notation "nativeCode" => M.nativeCode leaf bottom x input widths order fits
local notation "arena" => reader.startupArenaWith (n:=n) (reg:=reg) physical a link L.header
local notation "fresh" => StartupArena.next arena + 7*D.candidates
variable (gateCeiling : ℕ)
local notation "table" => reservedGeometryTable history slots fits emit x gateCeiling
local notation "off" => StartupArena.literal arena/4
local notation "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size table) o b*W) r
local notation "st" => Allocation.stripe fresh reserve (Table.size table) o b off ell
local notation "extWords" => fun u : Fin (teams+1) => Allocation.fields (old u) fresh reserve (Table.size table) o b off ell
local notation "place" => fun u : Fin (teams+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extWords u)
local notation "geometryBits" => fun _ : Fin (teams+1) => GeometryAdvice.serialized (GeometryAdvice.packet (w := W)
  fresh (Allocation.packed fresh reserve (Table.size table) o b W) table (fun i => StartupArena.broadcastBase arena+1+Fin.val i))
variable (boot : GeometryAdvice.Stripe) (bootBits : Fin (teams+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)
local notation "start" => freeStartWith physical r 32 reg W n
local notation "sites" => reader.startupSitesWith physical P S place fit D boot st bootBits geometryBits strings L.header
variable {claimsDim : ℕ} (word : Fin reserve → Bool) (decl : List Bool) (countBits extra : ℕ)
variable (claims : Fin (teams+1) → Fin claimsDim → ℕ)
local notation "hdr" => JointHeader.padded (JointHeader.evaluation (List.ofFn word++decl) countBits claims) extra

include project front_eq in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3200000 in
/-- The augmented geometry program accepts precisely the original public history codes,
even on an arbitrary assignment of the other exterior wires. All its physical
pin guesses, retained boot operands and terminal RAM rows belong to the same
history as the one decoded from the common header. -/
theorem ChosenReader.projected_profile_startupReservedCommonWith
    (gateFit : (geometryTable history slots fits emit x).size ≤ gateCeiling) (length : (hdr).length = L.header)
    (wire : Exterior teams r link → Bool)
    (common : ∀ b, (L.exteriorEquiv wire).broadcast b = JointHeader.headerBits hdr length) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot st) (copies : reader.packetBitCount ≤ r) (width : b ≤ W)
    (endFits : Allocation.stop fresh reserve gateCeiling o b W < 2^W) :
    let T := sites
    let B := reader.siteOperandsWith physical P S place fit L.header u
    let p := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let exterior := wire
    let F := G.processorFields u pin exterior B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    let returned := Returns (Evaluator.withStartup pinGeometry) pub mac bank initial
    let time := jointBudget p.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
      GeometryAdviceRate.ticks gateCeiling reserve o b W)
    let dest := Allocation.dest fresh reserve gateCeiling o b
    (Nonempty returned ↔ ∃! q, (nativeCode q).val = word) ∧
    ∀ q, (nativeCode q).val = word → ∃ paths : (Fin B.layout.guessWidth → Bool) ≃ returned, ∀ guess,
      let out := paths guess
      let mem := out.val.2.2
      out.val.1.flatMap TeamRAM.Event.choices = List.ofFn guess ∧ traceCost out.val.1 ≤ time ∧ signedWeight out.val.1 = 1 ∧
      (∃ trace z saved, Runs pub mac JointHeader.bootHeader bank initial trace z saved ∧
        JointHeader.BootHeaderState F f B.advice p pub hdr z saved ∧
        ∀ i < (arena).next, mem i = Pins.preparedMemory B.layout (Pins.extendGuess guess) saved B.layout.count i) ∧
      JointHeader.FlatAt mem f.dst hdr ∧
      (∃ passed, (nativeCode).symm ⟨profileRAM mem f.dst,passed⟩ = q) ∧
      ∀ i, readings mem (dest+i.val) = ParseBatchSort.value (fun j => emit.eval
        (Sum.elim (Sum.elim x word) (output aug rounds le_rfl (repeatLeaf (fan sched) front rounds) x (M.packBits leaf rounds le_rfl q))) (i,j)) := by
  intro T B p pub G exterior F f initial returned time dest
  have program := reader.profile_startupReservedCommonWith (gap := 7*D.candidates) physical P S fit valuation entry totals old L history
    slots fits emit x gateCeiling gateFit D boot bootBits strings word decl countBits extra claims length wire common u pin mac bank regions copies width endFits
  obtain ⟨accept,outputs⟩ := M.projected_native_profile_outputs leaf bottom x input widths order fits pick aug project front front_eq emit word
    (Evaluator.withStartup pinGeometry) B.layout.guessWidth pub mac bank initial time dest program
  refine ⟨accept,fun q eqn => ?_⟩
  obtain ⟨E,hE⟩ := outputs q eqn
  refine ⟨E,fun guess => ?_⟩
  obtain ⟨bitsEq,ticks,sign,post,rows⟩ := hE guess
  obtain ⟨tr,z,saved,run,bootState,memEq⟩ := post
  have original := reader.siteOperands_arenaWith physical P S fit valuation entry totals extWords L u
  have clear := (arena_pin_clear arena u (adviceOffsetWith physical r 32 reg W n) p).2.2
  rw [← original] at clear
  have chdr : PinClear B.layout f.dst (hdr).length := length ▸ clear
  have before : f.dst+(hdr).length ≤ (arena).next := by
    rw [length]
    change (arena).broadcastBase+L.header ≤ (arena).next
    unfold StartupArena.next StartupArena.hbase StartupArena.ibase
    exact Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _)
  have copy : JointHeader.FlatAt (E guess).val.2.2 f.dst hdr := fun i =>
    (memEq (f.dst+i.val) (by have h := i.isLt; omega)).trans
      ((PinClear.read chdr (Pins.extendGuess guess) saved i.val i.isLt).trans (bootState.header i))
  have hw : 0<W := by
    have ceiling : (arena).next < 2^W := by
      apply lt_of_le_of_lt _ endFits
      unfold Allocation.stop Allocation.packed Allocation.dense Allocation.dest Allocation.temp
      omega
    have one : 1 ≤ (arena).next := by rw [StartupArena.next_eq]; omega
    by_contra! h
    have power := one.trans_lt ceiling
    rw [Nat.eq_zero_of_le_zero h] at power
    omega
  have copyQ := copy
  rw [← eqn] at copyQ
  have decoded := M.copied_profile_RAM leaf bottom x input widths order fits hw q decl claims copyQ
  exact ⟨bitsEq,ticks,sign,⟨tr,z,saved,run,bootState,memEq⟩,copy,decoded.1,rows⟩

end Diagonal

end BorderVNP
end Computability
end OAI

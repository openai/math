import OAI.Computability.BorderVNP.PackedHistoryChosenTableGeometry

/-! # The chosen timed processor starts the gate-padded geometry circuit

The selected finite-ring reference packet carries the addresses of the history circuit.
The actual team literal installs its gate list, and the real boot prefix copies the trial
profile from the common exterior header. Every returning path of the pin and history
prefix is accounted for, including its private substituted bits, clock and emitted rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput DiagonalResidueRAM
open VPVNP BurstRAM RAMTape TeamContraction TeamContraction.ProcessorSlots VerifierNetwork
open RoutingISA RoutingISA.Pins GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit
open scoped Classical

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
variable {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] {active reserve o b gap : ℕ}
variable (history : Frame (X ⊕ Y) (V ⊕ Unit)) (order : Y ≃ Fin active) (fits : active ≤ reserve)
variable (emit : Frame ((X ⊕ Fin reserve) ⊕ V) (Fin o × Fin b)) (x : X → Bool)
variable (gateCeiling : ℕ) (gateFit : (geometryTable history order fits emit x).size ≤ gateCeiling)
local notation "arena" => reader.startupArenaWith (n := n) (reg := reg) physical a link L.header
local notation "fresh" => StartupArena.next arena + gap
local notation "table" => reservedGeometryTable history order fits emit x gateCeiling
local notation "off" => StartupArena.literal arena/4
local notation "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size table) o b*W) r
local notation "st" => Allocation.stripe fresh reserve (Table.size table) o b off ell
local notation "extWords" => fun u : Fin (teams+1) => Allocation.fields (old u) fresh reserve (Table.size table) o b off ell
local notation "place" => fun u : Fin (teams+1) =>
  ReaderPlacement.inArena arena (valuation u) (entry u) (totals u) (extWords u)
local notation "geometryBits" => fun _ : Fin (teams+1) => GeometryAdvice.serialized (GeometryAdvice.packet (w := W)
  fresh (Allocation.packed fresh reserve (Table.size table) o b W) table (fun i => StartupArena.broadcastBase arena+1+Fin.val i))
variable (D : Packing.Directory.Layout) (boot : GeometryAdvice.Stripe) (bootBits : Fin (teams+1) → List Bool)
variable (strings : Fin D.entries → Fin D.description → Bool)
local notation "start" => freeStartWith physical r 32 reg W n
local notation "sites" => reader.startupSitesWith physical P S place fit D boot st bootBits geometryBits strings L.header
variable {claimsDim : ℕ} (word : Fin reserve → Bool) (decl : List Bool) (countBits extra : ℕ)
variable (claims : Fin (teams+1) → Fin claimsDim → ℕ)
local notation "hdr" => JointHeader.padded (JointHeader.evaluation (List.ofFn word++decl) countBits claims) extra

private theorem profilePaths_eq {w count size : ℕ} {body : Code} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {bank : Bank w} {mem : Memory w}
    {resident : (Fin count → Bool) → Memory w → Prop} {p q : Prop} {t t' d d' : ℕ} {f g : Fin size → ℕ}
    (run : ProfilePaths body count pub mac bank mem p t d f resident)
    (guard : p ↔ q) (clock : t=t') (base : d=d') (words : f=g) :
    ProfilePaths body count pub mac bank mem q t' d' g resident := by
  rw [← propext guard,← clock,← base,← words]
  exact run

include gateFit in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3200000 in
/-- On any exterior carrying this common broadcast, the native pin and geometry
reader returns exactly at the accepted padded words. The other wires are arbitrary. -/
theorem ChosenReader.profile_startupReservedCommonWith (length : (hdr).length = L.header)
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
    let ok := validProfile order fits (fun g => history.eval (Sum.elim x g) (.inr ()) = true) word
    ProfilePaths (Evaluator.withStartup pinGeometry) B.layout.guessWidth pub mac bank initial ok
      (jointBudget p.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
        GeometryAdviceRate.ticks gateCeiling reserve o b W))
      (Allocation.dest fresh reserve gateCeiling o b) (emittedWords history order fits emit x word)
      (fun guess after => ∃ trace z saved, Runs pub mac JointHeader.bootHeader bank initial trace z saved ∧
        JointHeader.BootHeaderState F f B.advice p pub hdr z saved ∧
        ∀ i < (arena).next, after i = Pins.preparedMemory B.layout (Pins.extendGuess guess) saved B.layout.count i) := by
  intro T B p pub G exterior F f initial ok
  have size : (table).size=gateCeiling := (geometryTable history order fits emit x).reserve_size gateCeiling gateFit
  have endFits' : Allocation.stop fresh reserve (table).size o b W < 2^W := by rw [size]; exact endFits
  have run := reader.profile_startupTableCommonWith physical P S fit valuation entry totals old L table
    D boot bootBits strings word decl countBits extra claims length wire common u pin mac bank regions copies width endFits'
  obtain ⟨guard,rows⟩ := reserved_semantics history order fits emit x gateCeiling word
  change (GeometryOutput.validBit table (Sum.elim word Fin.elim0)=true ↔ ok) at guard
  exact profilePaths_eq run guard
    (congrArg (fun k => jointBudget p.bits.length W+f.readTicks+2+
      ((pinSetup.slots+17*B.layout.count+1)+GeometryAdviceRate.ticks k reserve o b W)) size)
    (congrArg (fun k => Allocation.dest fresh reserve k o b) size) rows

include gateFit in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3200000 in
/-- The complete startup, evaluation-mode dispatch, fresh substituted-index guess and guarded
history reader on the true joint signed site. The geometry is placed above the reserved
`gap` words, which accommodate the seven-word demand records. The statement starts with that site's genuine
RAM input image and accounts for every returning path of this evaluation prefix. -/
theorem ChosenReader.profile_startupReservedWith (length : (hdr).length = L.header)
    (payload : Fin (teams+1) → Fin (teams+1) → ℕ → Bool) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot st) (copies : reader.packetBitCount ≤ r) (width : b ≤ W)
    (endFits : Allocation.stop fresh reserve gateCeiling o b W < 2^W) :
    let T := sites
    let B := reader.siteOperandsWith physical P S place fit L.header u
    let p := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let exterior := JointHeader.exterior L hdr length payload
    let F := G.processorFields u pin exterior B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    let ok := validProfile order fits (fun g => history.eval (Sum.elim x g) (.inr ()) = true) word
    ProfilePaths (Evaluator.withStartup pinGeometry) B.layout.guessWidth pub mac bank initial ok
      (jointBudget p.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
        GeometryAdviceRate.ticks gateCeiling reserve o b W))
      (Allocation.dest fresh reserve gateCeiling o b) (emittedWords history order fits emit x word)
      (fun guess after => ∃ trace z saved, Runs pub mac JointHeader.bootHeader bank initial trace z saved ∧
        JointHeader.BootHeaderState F f B.advice p pub hdr z saved ∧
        ∀ i < (arena).next, after i = Pins.preparedMemory B.layout (Pins.extendGuess guess) saved B.layout.count i) := by
  exact reader.profile_startupReservedCommonWith physical P S fit valuation entry totals old L history
    order fits emit x gateCeiling gateFit D boot bootBits strings word decl countBits extra claims length
    (JointHeader.exterior L hdr length payload) (JointHeader.exterior_header L hdr length payload)
    u pin mac bank regions copies width endFits

end Diagonal

end BorderVNP
end Computability
end OAI

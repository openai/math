import OAI.Computability.BorderVNP.PackedHistoryReservedPaths
import OAI.Computability.BorderVNP.PackedHistoryBootPaths
import OAI.Computability.BorderVNP.TransmissionChosenPhysical

/-! # The chosen timed processor starts its explicitly supplied geometry table

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
variable {reserve o b gap : ℕ} (table : Table (Fin reserve ⊕ Fin 0) o b)
local notation "arena" => reader.startupArenaWith (n := n) (reg := reg) physical a link L.header
local notation "fresh" => StartupArena.next arena + gap
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

set_option maxRecDepth 4000 in
set_option maxHeartbeats 3200000 in
/-- The real profile interpreter accepts exactly the checked words on any common-header exterior, before route verification. -/
theorem ChosenReader.profile_startupTableCommonWith (length : (hdr).length = L.header)
    (wire : Exterior teams r link → Bool)
    (common : ∀ b, (L.exteriorEquiv wire).broadcast b = JointHeader.headerBits hdr length) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot st) (copies : reader.packetBitCount ≤ r) (width : b ≤ W)
    (endFits : Allocation.stop fresh reserve (table).size o b W < 2^W) :
    let T := sites
    let B := reader.siteOperandsWith physical P S place fit L.header u
    let p := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let exterior := wire
    let F := G.processorFields u pin exterior B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    let ok := GeometryOutput.validBit table (Sum.elim word Fin.elim0)=true
    ProfilePaths (Evaluator.withStartup pinGeometry) B.layout.guessWidth pub mac bank initial ok
      (jointBudget p.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
        GeometryAdviceRate.ticks (table).size reserve o b W))
      (Allocation.dest fresh reserve (table).size o b) (nativeTableWords table word)
      (fun guess after => ∃ trace z saved, Runs pub mac JointHeader.bootHeader bank initial trace z saved ∧
        JointHeader.BootHeaderState F f B.advice p pub hdr z saved ∧
        ∀ i < (arena).next, after i = Pins.preparedMemory B.layout (Pins.extendGuess guess) saved B.layout.count i) := by
  intro T B p pub G exterior F f initial ok
  have hdrLen : 1+reserve ≤ L.header := by
    rw [← length]; simp only [JointHeader.padded,List.length_append,JointHeader.evaluation_length,
      List.length_ofFn,List.length_replicate]; omega
  have positive : 0 < L.header := by omega
  have ceiling : (arena).next < 2^W := by
    apply lt_of_le_of_lt _ endFits
    unfold Allocation.stop Allocation.packed Allocation.dense Allocation.dest Allocation.temp; omega
  have fitsAll := reader.arena_fitsWith physical P S fit valuation entry totals extWords L u positive copies ceiling
  obtain ⟨tr,z,mz,run,tc,_,post,image⟩ := reader.arena_header_startupCommonWith physical P S fit valuation entry totals extWords
    L D boot st bootBits geometryBits strings hdr length wire common u pin mac bank regions positive copies ceiling
  have frame : (pub 0).val = (arena).frame := B.frameBase_word (S.publicWords u) fitsAll.1
  have original : B = (arena).operands u (adviceOffsetWith physical r 32 reg W n) p :=
    reader.siteOperands_arenaWith physical P S fit valuation entry totals extWords L u
  have clear := arena_pin_clear arena u (adviceOffsetWith physical r 32 reg W n) p
  rw [← original] at clear
  have cinput : PinClear B.layout 0 F.header.length := F.header_length ▸ clear.1
  have cframe : PinClear B.layout (pub 0).val 112 := frame ▸ clear.2.1
  have chdr : PinClear B.layout f.dst (hdr).length := length ▸ clear.2.2
  have before : f.dst+1+reserve ≤ (arena).next := by
    change (arena).broadcastBase+1+reserve ≤ (arena).next
    unfold StartupArena.next StartupArena.hbase StartupArena.ibase
    change _ ≤ (arena).broadcastBase+L.header+(arena).count+(arena).count; omega
  have literal : (arena).literal = D.literal := by
    rw [← regions.literal]
    change entryLiteral _ (W+1) n (prefixCapacity r 32 reg W n+1+a) = entryLiteral _ (W+1) n (prefixCapacity r 32 reg W n+1)+a
    simp only [entryLiteral,Nat.add_assoc]
  have hw : 0 < W := by
    have one : 1 < 2^W := (by omega : 1 ≤ B.frameBase+112).trans_lt fitsAll.2.2.2.1.frameBound
    by_contra! zero
    rw [Nat.eq_zero_of_le_zero zero] at one; omega
  have alloc : ProfileAllocation F f p pub D start a u.val boot (bootBits u) strings table
      fresh off ell (old u) := by
    refine ⟨image,rfl,?_,?_,before.trans (Nat.le_add_right _ _),width,?_,?_,?_,endFits⟩
    · rw [frame]; exact fitsAll.2.1
    · rw [frame]; exact Nat.le_add_right _ _
    · exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left ..)
    · have bounded := regions.geomEnd.trans (Nat.sub_le ..)
      exact bounded.trans_eq literal.symm
    · exact GeometryAdviceRate.stripe_capacity _ fitsAll.2.1.procs
  have mode : (mz f.dst).val ≠ 0 := by
    have core : JointHeader.FlatAt mz f.dst
        (JointHeader.spelling (List.ofFn word++decl) (DiagonalTallyRAM.broadcast countBits claims)) := post.header.left
    have zero := core ⟨0,by simp [JointHeader.spelling]⟩
    have one : mz f.dst = DiagonalResidueRAM.word W 1 := by simpa [JointHeader.spelling] using zero
    rw [one,DiagonalResidueRAM.word_val _ _ (Nat.one_lt_two_pow hw.ne')]; decide
  have inside := profile_paths_table table F f B.advice p pub mac (Function.update z 10 (mz f.dst)) mz
    word decl countBits extra claims (ProfileOperands.from_boot post) D start a u.val boot (bootBits u) strings
    fresh off ell (old u) alloc cinput cframe chdr fitsAll.2.2.2.2.2.2 fitsAll.2.2.2.2.1
  exact ((inside.with_startup f run post.registers mode).mono
    (Nat.add_le_add_right (Nat.add_le_add_right tc _) _)).map_memory (fun _ _ mem =>
      ⟨tr,z,mz,run,post,fun i hi => mem i (hi.trans_le (Nat.le_add_right _ _))⟩)

/-- The complete startup, evaluation-mode dispatch, fresh substituted-index guess and guarded
history reader on the true joint signed site. The geometry is placed above the reserved
`gap` words, which accommodate the seven-word demand records. The statement starts with that site's genuine
RAM input image and accounts for every returning path of this evaluation prefix. -/
theorem ChosenReader.profile_startupTableWith (length : (hdr).length = L.header)
    (payload : Fin (teams+1) → Fin (teams+1) → ℕ → Bool) (u : Fin (teams+1))
    (pin : Fin indexWidth → Bool) (mac : TeamOpcode.Macros W 8) (bank : Bank W)
    (regions : JointRoom D start a boot st) (copies : reader.packetBitCount ≤ r) (width : b ≤ W)
    (endFits : Allocation.stop fresh reserve (table).size o b W < 2^W) :
    let T := sites
    let B := reader.siteOperandsWith physical P S place fit L.header u
    let p := reader.packetAt (place u)
    let pub := T.publicWords u
    let G := wiringWith physical P T indexWidth link n e fit
    let exterior := JointHeader.exterior L hdr length payload
    let F := G.processorFields u pin exterior B.layout.ibase B.layout.hbase B.layout.starbase
    let f := G.transferFrame u L.header B.broadcastBase
    let initial := RAMMemory.initialMemory F.header.length (TeamTapeInputEmit.headerWord W F.header)
    let ok := GeometryOutput.validBit table (Sum.elim word Fin.elim0)=true
    ProfilePaths (Evaluator.withStartup pinGeometry) B.layout.guessWidth pub mac bank initial ok
      (jointBudget p.bits.length W+f.readTicks+2+((pinSetup.slots+17*B.layout.count+1)+
        GeometryAdviceRate.ticks (table).size reserve o b W))
      (Allocation.dest fresh reserve (table).size o b) (nativeTableWords table word)
      (fun guess after => ∃ trace z saved, Runs pub mac JointHeader.bootHeader bank initial trace z saved ∧
        JointHeader.BootHeaderState F f B.advice p pub hdr z saved ∧
        ∀ i < (arena).next, after i = Pins.preparedMemory B.layout (Pins.extendGuess guess) saved B.layout.count i) := by
  exact reader.profile_startupTableCommonWith physical P S fit valuation entry totals old L table
    D boot bootBits strings word decl countBits extra claims length (JointHeader.exterior L hdr length payload)
    (JointHeader.exterior_header L hdr length payload) u pin mac bank regions copies width endFits

end Diagonal

end BorderVNP
end Computability
end OAI

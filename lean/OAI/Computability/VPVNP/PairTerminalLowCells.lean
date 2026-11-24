import OAI.Computability.VPVNP.PairTerminalPrefixLinked
import OAI.Computability.VPVNP.PairTerminalFootprint
import OAI.Computability.VPVNP.PairSimulationPhysicalScanData
import OAI.Computability.VPVNP.LiveCompressedPairFrames
import OAI.Computability.VPVNP.PairTerminalShadowChronology

/-!
# Preservation of the low counter addresses before vertex evaluation

The terminal bootstrap writes its high header. The prefix scan writes its
offset array and the total and role fields in that header. The row builder
preserves lower addresses, and the shared scan writes only the final wire
bank. This leaves the live grammar and motif words available to the first
vertex burst.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix.Linked
open BurstRAM Compression LiveProgram CompressorRecords SourceTransport TerminalLink
open scoped Fin.CommRing

variable {w a g cap f : ℕ} {workers : TerminalLink.Stage → PairTable} {ports : Fin 11 → Word w} {X : State a g}
  {dir : IncidenceDirectory w} {starts : Word w} {input : Memory w} {raw : Report w} {rs : List (Report w)}

theorem Start.prefix_below (s : Start workers ports cap f X dir starts input raw rs)
    (room : (header ports).val+32 ≤ 2^w) (i : ℕ) (low : i < (header ports).val)
    (before : i < starts.val) (boot : after input raw.events i = input i) :
    prefixMemory ports input raw rs i = input i := by
  have fit : (header ports).val+31 < 2^w := by omega
  have cell := TerminalFootprint.below (header ports) fit low
  have h12 : i ≠ (Worker.header ports+12).val := by
    change i ≠ (header ports + (12 : Word w)).val
    have eq : (header ports + (12 : Word w)).val = (header ports).val + 12 :=
      TerminalFootprint.header_val _ fit (j := 12) (by decide)
    rw [eq]
    omega
  have h14 : i ≠ (Worker.header ports+14).val := by
    change i ≠ (header ports + (14 : Word w)).val
    have eq : (header ports + (14 : Word w)).val = (header ports).val + 14 :=
      TerminalFootprint.header_val _ fit (j := 14) (by decide)
    rw [eq]
    omega
  have agree := (s.scan.agree i cell).symm
  change prefixMemory ports input raw rs i = after (after input raw.events) (eventLog rs) i at agree
  rw [agree,s.rawScan.stored.outside i h12 (Or.inl before)]
  simpa only [writeMemory,ite_eq_right h14] using boot

end PairSimulation.TerminalPrefix.Linked

namespace PairSimulation.SharedBitPhase
open BurstRAM CompressorRecords SourceTransport TerminalLink

theorem below_bank {w : ℕ} (shape : DescriptorSpace.Shape) (limit : ℕ) (S : VertexImage.Part → VertexImage.Segment)
    (ports : Fin 11 → Word w) (cap : ℕ) (src phy : Memory w) {lo count : ℕ}
    (layout : FinalBits.Worker.Layout ports src lo count) (clock : 54 ≤ cap)
    (room : (header ports).val+32 ≤ 2^w) (below : lo+count ≤ (header ports).val)
    (agree : Agree (workerCell (header ports)) src phy)
    (valid : (Entry.resume Stage.sharedBits (0 : Word w)).Valid (header ports) phy)
    (f : Fin count → Bool) (i : ℕ) (hi : i < lo) :
    (equiv shape limit S ports cap src phy layout clock room below agree f).val.memory i = phy i := by
  have cell : workerCell (header ports) i := TerminalFootprint.below _ (by omega) (by omega)
  exact ((memory_image shape limit S ports cap src phy layout clock room below agree valid f) i cell).symm.trans
    ((FinalBits.outside lo layout.fits f src i (Or.inl hi)).trans (agree i cell))


/-- The vertex worker can replay its source on the post-scan physical
memory. At addresses below the workspace the bootstrap, prefix, row,
shared-bit and replay steps all preserve the original input word. -/
theorem vertex_source_below {w a g f₀ : ℕ} (shape : DescriptorSpace.Shape) (limit : ℕ)
    (S : VertexImage.Part → VertexImage.Segment) (ports : Fin 11 → Word w) (cap : ℕ)
    {X : Compression.State a g} {dir : IncidenceDirectory w} {starts : Word w}
    {input : Memory w} {boot : Report w} {prefixRows : List (Report w)}
    (start : TerminalPrefix.Linked.Start (TerminalProgram.workers shape limit S) ports cap f₀ X dir starts input boot prefixRows)
    (src phy : Memory w) {lo : ℕ}
    (layout : FinalBits.Worker.Layout ports src lo X.totalWidth) (clock : 54 ≤ cap)
    (room : (header ports).val+32 ≤ 2^w) (below : lo+X.totalWidth ≤ (header ports).val)
    (agree : Agree (workerCell (header ports)) src phy)
    (valid : (Entry.resume Stage.sharedBits (0 : Word w)).Valid (header ports) phy)
    (bits : Fin X.totalWidth → Bool) (vertexSrc : Memory w)
    (atVertex : Agree (workerCell (header ports)) vertexSrc
      (equiv shape limit S ports cap src phy layout clock room below agree bits).val.memory)
    (i : ℕ) (wireLow : i < lo) (indexLow : i < starts.val)
    (bootCell : after input boot.events i = input i)
    (rowCell : phy i = TerminalPrefix.Linked.prefixMemory ports input boot prefixRows i) :
    vertexSrc i = input i := by
  have hH : i < (header ports).val := by omega
  have cell := TerminalFootprint.below (header ports) (by omega) hH
  exact (atVertex i cell).trans ((below_bank shape limit S ports cap src phy layout clock room below agree valid bits i wireLow).trans
    (rowCell.trans (start.prefix_below room i hH indexLow bootCell)))

end PairSimulation.SharedBitPhase

namespace LiveProgram.CompressedPair
open BurstRAM Compression PairSimulation CompressorRecords SourceTransport
open PairStages.Group PairStages.Group.CompressedPaths

/-- Every live counter lies below the auxiliary shadow and the compression
workspace. The low part of the word-address layout fits without wraparound. -/
theorem counter_before_pairTag (G : PairStages.Group) (fit : Auxiliary.shadowBase G < 2^G.w)
    (a : Fin (labelCount G)) :
    Auxiliary.counterBase G + a.val < (PairTag.address (publicWords G)).val := by
  rw [show PairTag.address (publicWords G) = Pieces.word G.g G.lit (.geometry (Layout.oldState G.constants)) from
    tag_address G.constants G.g G.lit]
  have old : (Layout.oldState G.constants).eval G.g < 2^G.w := (Auxiliary.counter_end_le_shadow G).trans_lt fit
  change Auxiliary.counterBase G + a.val < (Layout.oldState G.constants).eval G.g % 2^G.w
  rw [Nat.mod_eq_of_lt old]
  exact Nat.add_lt_add_left a.isLt _


/-- The source word handed to the terminal bootstrap at a live counter
equals the original prepared nomination or zero motif word. -/
theorem online_counter_initial {d initial phases : ℕ} {C : Schedule.Catalog d}
    (b : Bootstrap) (plan : Schedule.Online.Config C initial phases) (terminal : PairTable)
    (G : PairStages.Group) (B n : ℕ) (m : Memory G.w)
    (runs : TransferredStartup.Runs (bootstrapRows b initial phases) d
      (startupLayout b initial phases B n ((publicWords G) 2).val) B n b.degreeBits b.lanesPerBlock b.steps
      (publicWords G) (PairTag.address (publicWords G)) m)
    {clock : ℕ} (path : StagePaths b plan terminal (publicWords G) clock Stage.online
      (afterStartup b (publicWords G) B n m initial phases d))
    (rs : List (Report G.w))
    (reported : LiveStageLink.ordinaryReports path = OnlineWorkspace.framed ((publicWords G) 2)
      (afterStartup b (publicWords G) B n m initial phases d) rs)
    (stable : SourceBankFrame.Stable (((publicWords G) 2).val+6)
      (afterStartup b (publicWords G) B n m initial phases d) rs)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) (a : Fin (labelCount G)) :
    onlinePost path (Auxiliary.counterBase G+a.val) = m (Auxiliary.counterBase G+a.val) := by
  let c := G.constants
  let g := G.g
  have sh : (Layout.shadow c).eval g < (Layout.pairWorkspace c).eval g :=
    Nat.lt_add_of_pos_right (Nat.two_pow_pos _)
  have tag := counter_before_pairTag G (sh.trans fit) a
  have ws : ((publicWords G) 2).val = (Layout.pairWorkspace c).eval g := Nat.mod_eq_of_lt fit
  have low : Auxiliary.counterBase G+a.val < ((publicWords G) 2).val := by
    rw [ws]
    exact ((Nat.add_lt_add_left a.isLt _).trans_le (Auxiliary.counter_end_le_shadow G)).trans sh
  exact onlinePost_after_startup_below b plan terminal (publicWords G) B n m runs path rs reported stable _ low tag.ne

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI

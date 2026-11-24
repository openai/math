import OAI.Computability.VPVNP.PairTerminalShadowTransfer
import OAI.Computability.VPVNP.LiveCompressedPairStartupFootprint
import OAI.Computability.VPVNP.CompressorSourceBankFrame

/-!
# The prepared shadow at the terminal handoff

The eight startup reports preserve cells below the compression workspace,
apart from the pair tag. The framed online reports have the memory effect of
their raw calendar reports. Their low-cell frame and the separate tag write
at handoff preserve both the histogram descriptor and each shadow word read
by the terminal evaluator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM CompressorRecords Schedule LiveStageLink

variable {w d initial phases : ℕ} {C : Catalog d}

/-- Online's incoming memory after the actual eight startup calls. -/
noncomputable abbrev afterStartup (b : Bootstrap) (pub : Fin 11 → Word w) (B n : ℕ)
    (m : Memory w) (initial phases d : ℕ) :=
  after m (eventLog (cursorStartupLogs b pub B n (pub 2).val m initial phases d))

/-- A protected address below the startup workspace survives the raw online
calendar, its six-pointer framing, and the transfer to the terminal stage. -/
theorem onlinePost_after_startup_below (b : Bootstrap) (plan : Online.Config C initial phases)
    (finalTable : PairTable) (pub : Fin 11 → Word w) (B n : ℕ) (m : Memory w)
    (runs : TransferredStartup.Runs (bootstrapRows b initial phases) d
      (startupLayout b initial phases B n (pub 2).val) B n b.degreeBits b.lanesPerBlock b.steps pub
      (PairTag.address pub) m)
    {clock : ℕ} (a : StagePaths b plan finalTable pub clock Stage.online (afterStartup b pub B n m initial phases d))
    (rs : List (Report w))
    (reported : ordinaryReports a = OnlineWorkspace.framed (pub 2) (afterStartup b pub B n m initial phases d) rs)
    (stable : SourceBankFrame.Stable ((pub 2).val+6) (afterStartup b pub B n m initial phases d) rs)
    (x : ℕ) (below : x < (pub 2).val) (apart : x ≠ (PairTag.address pub).val) :
    onlinePost a x = m x := by
  let start := afterStartup b pub B n m initial phases d
  have raw : after start (eventLog rs) x = start x := by
    simpa only [List.take_length] using stable.take_eq rs.length x (by omega)
  rw [onlinePost, show next Stage.online = some Stage.terminal from rfl, transferMemory, writeMemory, ite_eq_right apart,
    reported, (OnlineWorkspace.framed_effect (pub 2) start rs none).2.1, raw]
  exact cursorStartup_after_below b pub B n (pub 2).val m runs x below apart

end LiveProgram.CompressedPair

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PrimedInputRAM LiveAuxiliaryHeaders PairSimulation CompressorRecords Schedule LiveStageLink
open scoped Fin.CommRing

/-- The pair tag is the first old-state word, strictly before the shadow. -/
theorem pairTag_lt_shadow (G : Group) (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) :
    (PairTag.address (terminalOperands G)).val < (terminalOperands G 3).val := by
  have low : (Layout.oldState G.constants).eval G.g < shadowBase G := by
    simp only [shadowBase,Layout.shadow,Layout.orderMap,Layout.packedPrefix,Layout.adviceFrames,
      Layout.transitionScratch,Layout.newState,eval_add]
    change _ < _ + _ + _ + 5 + 24 + _ + _
    omega
  have high : shadowBase G ≤ (Layout.pairWorkspace G.constants).eval G.g := by
    change _ ≤ shadowBase G + _
    omega
  rw [CompressedPair.tag_address]
  exact lt_of_eq_of_lt (Nat.mod_eq_of_lt (low.trans (high.trans_lt fit)))
    (lt_of_lt_of_eq low (Nat.mod_eq_of_lt (high.trans_lt fit)).symm)

/-- A virtual header fitting the number of virtual sites ends before the
online workspace. The address-fit hypothesis recovers the natural addresses
from their machine-word representations. -/
theorem shadow_span_room (G : Group) (i : Fin (2^(sizes G).h))
    (hn : 1 ≤ G.g.n) (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w)
    (capacity : span (pairLengths G i) (histLength G) ≤ 2^(virtualSiteExponent G.g.d G.g.n)) :
    (terminalOperands G 3).val+span (pairLengths G i) (histLength G) ≤ (terminalOperands G 2).val := by
  have total : (Layout.pairWorkspace G.constants).eval G.g =
      shadowBase G + 2^(virtualSiteExponent G.g.d G.g.n) := by
    change shadowBase G + 2^(Layout.virtualSiteBits.eval G.g) = _
    rw [Layout.virtualSiteBits_eq G.g hn]
  have shadowFit : shadowBase G < 2^G.w := by omega
  have shadowVal : (terminalOperands G 3).val = shadowBase G := Nat.mod_eq_of_lt shadowFit
  have workspaceVal : (terminalOperands G 2).val = (Layout.pairWorkspace G.constants).eval G.g := Nat.mod_eq_of_lt fit
  rw [shadowVal, workspaceVal, total]
  exact Nat.add_le_add_left capacity _

variable {G : Group} {m : Memory G.w} {i : Fin (2^(sizes G).h)}
  {hdr : Header (pairLengths G i) → Bool}
  {N : Indexed G Stage.nominations m (Nominations.Nom G)} {μ : Nominations.Nom G}
  {d initial phases : ℕ} {C : Catalog d} {b : CompressedPair.Bootstrap}
  {plan : Online.Config C initial phases} {finalTable : PairTable} {clock : ℕ}

variable (B : PreparedBranch G m i hdr N μ) (blocks n : ℕ)
variable (runs : TransferredStartup.Runs (CompressedPair.bootstrapRows b initial phases) d
  (CompressedPair.startupLayout b initial phases blocks n (terminalOperands G 2).val)
  blocks n b.degreeBits b.lanesPerBlock b.steps (terminalOperands G)
  (PairTag.address (terminalOperands G)) (B.copy.memory ()))
variable (a : CompressedPair.StagePaths b plan finalTable (terminalOperands G) clock CompressedPair.Stage.online
  (CompressedPair.afterStartup b (terminalOperands G) blocks n (B.copy.memory ()) initial phases d))
variable (rs : List (Report G.w))
variable (reported : ordinaryReports a = OnlineWorkspace.framed (terminalOperands G 2)
  (CompressedPair.afterStartup b (terminalOperands G) blocks n (B.copy.memory ()) initial phases d) rs)
variable (stable : SourceBankFrame.Stable ((terminalOperands G 2).val+6)
  (CompressedPair.afterStartup b (terminalOperands G) blocks n (B.copy.memory ()) initial phases d) rs)

include runs reported stable in
/-- The terminal bootstrap computes the original header and histogram span
on the actual post-memory of the completed online path. -/
theorem PreparedBranch.shadowSpan_onlinePost
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) :
    TerminalBootstrap.shadowSpan (terminalOperands G) (CompressedPair.onlinePost a) =
      ((span (pairLengths G i) (histLength G) : ℕ) : Word G.w) := by
  apply B.shadowSpan_of_cell
  exact CompressedPair.onlinePost_after_startup_below b plan finalTable (terminalOperands G)
    blocks n _ runs a rs reported stable _ (histogramTarget_lt_workspace G fit) (histogramCell_lt_tag G fit).ne

include runs reported stable in
/-- Every populated or padded word within the shadow span reads as the
original auxiliary header or histogram at the terminal handoff. -/
theorem PreparedBranch.shadowRead_onlinePost
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w)
    (room : (terminalOperands G 3).val+span (pairLengths G i) (histLength G) ≤ (terminalOperands G 2).val)
    (j : ℕ) (hj : j < span (pairLengths G i) (histLength G)) :
    CompressedPair.onlinePost a ((terminalOperands G 3).val+j) =
      headerMemory (pairLengths G i) hdr (histogram G μ) j := by
  have before := pairTag_lt_shadow G fit
  exact (CompressedPair.onlinePost_after_startup_below b plan finalTable (terminalOperands G)
    blocks n _ runs a rs reported stable _ (by omega) (by omega)).trans (B.shadowRead j)

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI

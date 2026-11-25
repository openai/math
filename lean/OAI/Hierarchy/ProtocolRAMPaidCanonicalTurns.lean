import OAI.Hierarchy.ProtocolRAMPaidOriginalEndpoints
import OAI.Hierarchy.ProtocolRAMPaidTurnCoordinates
import OAI.Hierarchy.ProtocolRAMTurnCanonicalGeometry

namespace OAI
/-! # Authenticating the orientation and installed site of a live terminal turn -/

noncomputable section
namespace Hierarchy.ProtocolRAMPaidTurnPlacement.Canonical
open AdaptiveProbe ProbeStage CoreBoard WordSeats ReportSockets HistoryRoles WireTelescope SettledMatrix
open ProtocolRAM.Calendar CoreRoute ProtocolRAMTurnOrder ProtocolRAMTurnChart ProtocolRAMTurnShelf
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical

variable {h W k attempts edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (uni : Exclusive mark)
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
local notation "inj" => Equiv.injective (siteNumber h (2^W) k)
local notation "Sources" => ProtocolRAMTurnGeometry.Source edges h (2^W) k
local notation "names" => Equiv.symm (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k)
local notation "len" => ProtocolRAMTurnGeometry.length ∘ names
local notation "direction" => ProtocolRAMTurnStepOrder.reverse B inj pad

theorem reverse_of_ends (v : Words) (i : ℕ) (src : Sources)
    (left : v.rawSource i = (originalEnd S π B pad src false).val)
    (right : v.rawTarget i = (originalEnd S π B pad src true).val) : rev v i = direction src := by
  rw [rev, left, right]
  rcases src with e | i | c
  · change decide (¬(filledChord B.actual pad e).1.1.val < (filledChord B.actual pad e).1.2.val) = false
    have low : (filledChord B.actual pad e).1.1.val < (filledChord B.actual pad e).1.2.val :=
      (filledChord B.actual pad e).property
    simp [low]
  · rfl
  · rfl

/-- Get the direction from both native source banks of the live original. -/
theorem reverse_captured {w : ℕ} (board : RoleProgram.Board) {old : Fin board.old → ℕ}
    {out : Fin board.edges → ℕ}
    {before : ∀ i, 0 < old i → Bool → Public S h W k attempts}
    {after : ∀ i, 0 < out i → Bool → Public S h W k attempts}
    {m : Computability.VPVNP.BurstRAM.Memory w} (live : board.LiveReads S old out before after m)
    (site half : ProtocolRAM.Bank) (i : Fin board.old) (on : 0 < old i) (src : Sources)
    (ends : ∀ b, HistoryRoles.name (HistoryRoles.site S (before i on b)) = originalEnd S π B pad src b)
    (fits : siteLast h (2^W) k+1 ≤ 2^w) :
    rev (captured (ProtocolRAMTurnSnapshot.chartData board site half) m) i.val = direction src := by
  apply reverse_of_ends S π B pad
  · exact (ProtocolRAMTurnSnapshot.source_at S board live site half i on false fits).trans (congrArg Fin.val (ends false))
  · exact (ProtocolRAMTurnSnapshot.source_at S board live site half i on true fits).trans (congrArg Fin.val (ends true))

end Hierarchy.ProtocolRAMPaidTurnPlacement.Canonical

end
end OAI

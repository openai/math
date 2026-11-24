import OAI.Computability.VPVNP.PairSimulationSharedBitPhase
import OAI.Computability.VPVNP.PairTerminalGatherGeometry

/-!
# Wire assignments of the terminal scan in a nomination trace

The earlier data scan makes one singleton choice per wire bit in descending
address order. The terminal worker appends one empty closing call and writes
those same bits to the selected physical bank. The construction includes
empty banks and zero-width edges.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.PhysicalScanData

open BurstRAM PrivateRAM Compression CompressorRecords LocalHistory

variable {a g w p r k : ℕ} (X : State a g)
  (M : Machine w p r k) (pc : Fin 10 → Fin p) (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p)
  (hl : FinalBits.Linked M pc reg base done) (he : M.entry = pc 0)
  (low : ℕ) (pub : M.publicData base = FinalBits.cursor w low 0) (m : Memory w) (extra : ℕ)
  (fit : low + X.totalWidth < 2 ^ w)

local notation "scan" => stateScanPhase X M pc reg base done hl he low pub m extra fit

private def resize {n t : ℕ} (h : n = t) : (Fin n → Bool) ≃ (Fin t → Bool) :=
  Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)

private theorem calls_resize {n t : ℕ} (h : n = t) (f : Fin n → Bool) :
    FinalBits.calls (resize h f) = FinalBits.calls f := by cases h; rfl

/-- Enumerate each successful data scan by its complete assignment in the state's address order. -/
noncomputable def assignment : (scan).Path ≃ (Fin X.totalWidth → Bool) :=
  (FinalBits.scanEquiv hl he low (∑ i, TerminalPrefix.width X i)
    (by rwa [TerminalPrefix.width_sum]) pub m extra).symm.trans
    (resize (TerminalPrefix.width_sum X))

local notation "bits" => assignment X M pc reg base done hl he low pub m extra fit

theorem calls (x : (scan).Path) : (scan).calls x = FinalBits.calls (bits x) := by
  let read := FinalBits.scanEquiv hl he low (∑ i, TerminalPrefix.width X i)
    (by rwa [TerminalPrefix.width_sum]) pub m extra
  change x.val = FinalBits.calls (resize (TerminalPrefix.width_sum X) (read.symm x))
  rw [calls_resize]
  exact congrArg Subtype.val (read.apply_symm_apply x).symm

/-- Grouping the flat assignment by outgoing arc gives the payload used by
the nomination's vertex witnesses. -/
theorem payload (x : (scan).Path) : (scan).payload x =
    TerminalGatherGeometry.payload X
      (fun i => bits x (Fin.cast (TerminalPrefix.width_sum X) i)) := by
  let read := FinalBits.scanEquiv hl he low (∑ i, TerminalPrefix.width X i)
    (by rwa [TerminalPrefix.width_sum]) pub m extra
  have heq : (fun i => bits x (Fin.cast (TerminalPrefix.width_sum X) i)) = read.symm x := by
    funext i
    change (read.symm x) (Fin.cast (TerminalPrefix.width_sum X).symm
      (Fin.cast (TerminalPrefix.width_sum X) i)) = (read.symm x) i
    rw [Fin.cast_cast, Fin.cast_refl]; rfl
  rw [heq, ← TerminalGatherGeometry.phase_payload X M pc reg base done hl he low pub m extra fit]
  exact congrArg (scan).payload (read.apply_symm_apply x).symm

open private payload_bit from OAI.Computability.VPVNP.PairTerminalGatherGeometry

/-- Physical ordinal of a bit within one edge's payload. -/
def index (e : X.network.Edge) (j : Fin (X.width ((e.1.1, e.2), e.1.2))) : Fin X.totalWidth :=
  Fin.cast (TerminalPrefix.width_sum X) (FinalBits.index (TerminalPrefix.width X)
    (TerminalGatherGeometry.number X e) (Fin.cast (TerminalGatherGeometry.scan_width X e).symm j))

theorem payload_bit_eq (x : (scan).Path) (e : X.network.Edge)
    (j : Fin (X.width ((e.1.1, e.2), e.1.2))) :
    (scan).payload x e j = bits x (index X e j) := by
  rw [payload X M pc reg base done hl he low pub m extra fit]
  exact payload_bit X _ e j

variable {width : ℕ} (F : DescriptorSpace.Shape) (limit : ℕ)
  (S : VertexImage.Part → VertexImage.Segment) (ops : Fin 11 → Word width) (cap : ℕ)
  (src phy : Memory width) (lo : ℕ) (layout : FinalBits.Worker.Layout ops src lo X.totalWidth)
  (clock : 54 ≤ cap) (room : (TerminalLink.header ops).val + 32 ≤ 2 ^ width)
  (below : lo + X.totalWidth ≤ (TerminalLink.header ops).val)
  (agree : SourceTransport.Agree (TerminalLink.workerCell (TerminalLink.header ops)) src phy)

/-- Transport nomination data directly to a completed shared-bit record of
the terminal program, allowing independent word sizes and base addresses. -/
noncomputable def physical :
    (scan).Path ≃ TerminalLink.CompletedPhase (TerminalProgram.workers F limit S) ops cap
      (.resume TerminalLink.Stage.sharedBits 0) phy :=
  (bits).trans (SharedBitPhase.equiv F limit S ops cap src phy layout clock room below agree)

local notation "linked" => physical X M pc reg base done hl he low pub m extra fit F limit S
  ops cap src phy lo layout clock room below agree

theorem physical_choices (x : (scan).Path) :
    (linked x).val.choices = (scan).calls x ++ [[]] := by
  rw [calls X M pc reg base done hl he low pub m extra fit]
  rfl

/-- Physical readback from the chosen phase yields the bit of the actual
payload supplied to both incident vertex witnesses. -/
theorem physical_payload (x : (scan).Path) (e : X.network.Edge)
    (j : Fin (X.width ((e.1.1, e.2), e.1.2)))
    (valid : (TerminalLink.Entry.resume TerminalLink.Stage.sharedBits (0 : Word width)).Valid
      (TerminalLink.header ops) phy) :
    (linked x).val.memory (lo + (index X e j).val) = PrimedInputRAM.encodeBit width
      ((scan).payload x e j) := by
  rw [payload_bit_eq X M pc reg base done hl he low pub m extra fit]
  exact SharedBitPhase.readback F limit S ops cap src phy layout clock room below agree valid _ _

end PairSimulation.PhysicalScanData

end VPVNP
end Computability
end OAI

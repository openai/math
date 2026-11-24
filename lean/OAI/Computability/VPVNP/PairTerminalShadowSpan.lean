import OAI.Computability.VPVNP.LiveProgramPairPreparation
import OAI.Computability.VPVNP.PairTraversalTerminalBootstrap

/-! # The auxiliary header length recovered by the terminal pair program

The histogram target is the third word of the seventh auxiliary descriptor.
Subtracting the shadow base from that target recovers the reserved bit-header
length, including both padded exterior cuts. The pair operand supplying the
histogram length completes the span used to bound a leaf's external read.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PrimedInputRAM LiveAuxiliaryHeaders PairSimulation
open scoped Fin.CommRing

/-- The eleven public words supplied to the terminal pair program. -/
abbrev terminalOperands (G : Group) := Pieces.word G.g G.lit ∘ StageOperands.pair G.constants

/-- The word preceding the counter base is the histogram's descriptor target. -/
theorem histogramTargetAddress (G : Group) :
    terminalOperands G 4 - 1 = LiveHeaderCopyDispatch.address (desc G) 6 2 := by
  change ((counterBase G : ℕ) : Word G.w) - 1 = ((tableBase G : ℕ) : Word G.w) + 20
  rw [← (geometry_order G).2.2.1, Nat.cast_add, Nat.cast_ofNat]
  ring

variable {G : Group} {m : Memory G.w} {i : Fin (2^(sizes G).h)}
  {hdr : Header (pairLengths G i) → Bool}
  {N : Indexed G Stage.nominations m (Nominations.Nom G)} {μ : Nominations.Nom G}

/-- Actual word computed by the eleven-operand terminal bootstrap on the
memory returned by the native auxiliary initializer and copy sweep. -/
theorem PreparedBranch.shadowSpan (B : PreparedBranch G m i hdr N μ) :
    TerminalBootstrap.shadowSpan (terminalOperands G) (B.copy.memory ()) =
      ((span (pairLengths G i) (histLength G) : ℕ) : Word G.w) := by
  unfold TerminalBootstrap.shadowSpan
  rw [histogramTargetAddress, B.descriptorFrame, B.copyPrepared.descriptors.targets]
  change (((shadow G).val + Header.count (pairLengths G i) : ℕ) : Word G.w) - shadow G +
      (histLength G : Word G.w) = ((Header.count (pairLengths G i) + histLength G : ℕ) : Word G.w)
  rw [Nat.cast_add, Nat.cast_add]
  have word : ((shadow G).val : Word G.w) = shadow G := Fin.cast_val_eq_self _
  rw [word]
  abel

/-- The histogram descriptor is strictly below the compression workspace. -/
theorem histogramTarget_lt_workspace (G : Group)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) :
    (terminalOperands G 4 - 1).val < (terminalOperands G 2).val := by
  have hw : (terminalOperands G 2).val = (Layout.pairWorkspace G.constants).eval G.g :=
    Nat.mod_eq_of_lt fit
  have hp : shadowBase G ≤ (Layout.pairWorkspace G.constants).eval G.g := by
    change _ ≤ shadowBase G + _
    omega
  obtain ⟨_,_,he,hs⟩ := geometry_order G
  rw [histogramTargetAddress, hw]
  have hd : (desc G).val = tableBase G := Nat.mod_eq_of_lt (show tableBase G < 2^G.w by omega)
  rw [LiveAuxiliaryDescriptorInit.address_val _ (by omega), hd]
  change tableBase G + 20 < _
  omega

/-- Changes confined to the compression workspace preserve the recovered span. -/
theorem PreparedBranch.shadowSpan_of_frame (B : PreparedBranch G m i hdr N μ)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) {mem : Memory G.w}
    (frame : ∀ a < (terminalOperands G 2).val, mem a = B.copy.memory () a) :
    TerminalBootstrap.shadowSpan (terminalOperands G) mem =
      ((span (pairLengths G i) (histLength G) : ℕ) : Word G.w) := by
  rw [← B.shadowSpan]
  unfold TerminalBootstrap.shadowSpan
  rw [frame _ (histogramTarget_lt_workspace G fit)]

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI

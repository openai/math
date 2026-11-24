import OAI.Computability.VPVNP.PairNativeFrameDescriptor
import OAI.Computability.VPVNP.PairTerminalShadowSpan

/-! # Preservation of terminal geometry and auxiliary shadow through vertex calls -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary
open BurstRAM PairSimulation NativeFrame
open scoped Fin.CommRing

variable (G : Group)

private theorem shadow_le_workspace : shadowBase G ≤ (Layout.pairWorkspace G.constants).eval G.g := by
  change shadowBase G ≤ shadowBase G + _
  exact Nat.le_add_right _ _

/-- The three physical public operands describing the counter bank cannot
reach the auxiliary shadow, hence cannot reach the high terminal header. -/
theorem physical_counter_end (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) :
    let pub := terminalOperands G
    (pub 4).val + (pub 5).val + G.constants.motifLabels ≤ (pub 3).val ∧
      (pub 3).val ≤ (pub 2).val ∧ (pub 9).val = G.constants.motifLabels := by
  intro pub
  have endLe := counter_end_le_shadow G
  change counterBase G + (histLength G + G.constants.motifLabels) ≤ shadowBase G at endLe
  have sw := shadow_le_workspace G
  have shadowFit : shadowBase G < 2^G.w := sw.trans_lt fit
  have h3 : (pub 3).val = shadowBase G := Nat.mod_eq_of_lt shadowFit
  have h4 : (pub 4).val = counterBase G := Nat.mod_eq_of_lt (show counterBase G < 2^G.w by omega)
  have h5 : (pub 5).val = histLength G := Nat.mod_eq_of_lt (show histLength G < 2^G.w by omega)
  have h9 : (pub 9).val = G.constants.motifLabels := Nat.mod_eq_of_lt (show G.constants.motifLabels < 2^G.w by omega)
  have h2 : (pub 2).val = (Layout.pairWorkspace G.constants).eval G.g := Nat.mod_eq_of_lt fit
  rw [h2,h3,h4,h5,h9]; exact ⟨by omega,sw,rfl⟩

variable {G} {m : Memory G.w} {header span : Word G.w} {row rowWords stride baseRadix laneRadix : ℕ}

/-- Readback of the same six native header fields after the actual motif
counter update, using the physical counter allocation of the live program. -/
theorem readback_after_histogram (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w)
    (below : (terminalOperands G 2).val ≤ header.val) (room : header.val+32 ≤ 2^G.w)
    (h : Readback m header row rowWords stride baseRadix laneRadix span) (hist : Fin G.constants.motifLabels → ℕ) :
    Readback (Counters.addHistogram (terminalOperands G 4).val (terminalOperands G 5).val hist m)
      header row rowWords stride baseRadix laneRadix span :=
  h.addHistogram _ _ hist (((physical_counter_end G fit).1.trans (physical_counter_end G fit).2.1).trans below) room

/-- Every address in the auxiliary shadow survives a site's native
counter flush, including reset addresses whose value is zero. -/
theorem shadow_after_histogram (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w)
    (hist : Fin G.constants.motifLabels → ℕ) (a : ℕ) :
    Counters.addHistogram (terminalOperands G 4).val (terminalOperands G 5).val hist m
      ((terminalOperands G 3).val + a) = m ((terminalOperands G 3).val + a) :=
  Counters.addHistogram_outside _ _ hist m _ (.inr ((physical_counter_end G fit).1.trans (Nat.le_add_right _ _)))

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI

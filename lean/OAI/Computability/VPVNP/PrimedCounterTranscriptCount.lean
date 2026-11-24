import OAI.Computability.VPVNP.PrimedCounterNative
import OAI.Computability.VPVNP.PrimedCounterTranscriptCountLabels
import OAI.Computability.VPVNP.RAMValidatorPaths

/-!
# The auxiliary RAM transcript computes the primed coefficient

The prescribed header is a word-valued function of site address. The
transcript validators first initialize RAM from that function. Their joint
path count, including all guesses at the auxiliary sites, is exactly the
grammar multiplicity for the original two groups and their exterior bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Data

open BurstRAM PrimedInputRAM

variable {L : Lengths} {n r H s w b d e : ℕ} {Q : Layout L n r H w}

/-- Capped auxiliary paths on the standard initialized header count the
multiplicity used in the grammar diagonal. -/
theorem transcript_count (D : Data Q s) (hf : D.Fits) (μ : GrammarDiagonal.Nomination n n b (Fin s))
    (hnom : D.nomination = GrammarDiagonal.exponents μ) (S K : ℕ) (hK : 15 ≤ K)
    (hbudget : 15 * D.total ≤ S*K) (hheader : Header.count L + D.labels ≤ S) :
    Nat.card (ActualPaths D.machine.program D.fuel 0 (RAMMemory.initialMemory S D.initial) (withinCaps S K)) =
      GrammarDiagonal.multiplicity D.degree D.root (PrimedInputRAM.input Q.program Q.fits D.header) μ := by
  rw [D.initialMemory_eq hheader]
  have he := D.native_count hf S K hK hbudget
  rw [hnom, GrammarDiagonal.coeff_exponents] at he
  exact_mod_cast he

/-- The product of the actual auxiliary validators' path counts, summed
over their shared-bit assignments, is the nominated integer coefficient. -/
theorem incident_count (D : Data Q s) (hf : D.Fits) (μ : GrammarDiagonal.Nomination n n b (Fin s))
    (hnom : D.nomination = GrammarDiagonal.exponents μ) (hK : 15 ≤ 2^e)
    (hbudget : 15 * D.total ≤ 2^d * 2^e) (hheader : Header.count L + D.labels ≤ 2^d)
    (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) :
    (∑ bits : RawAssignment d e w, ∏ v : Fin (2^d),
      Nat.card (D.machine.IncidentPaths D.fuel 0 (D.initial v) hw hc v (incidentBits bits v))) =
      GrammarDiagonal.multiplicity D.degree D.root (PrimedInputRAM.input Q.program Q.fits D.header) μ := by
  rw [← D.machine.parsimoniousIncidentPaths D.fuel 0 D.initial hw hc]
  exact D.transcript_count hf μ hnom _ _ hK hbudget hheader

end PrimedCounter.Data

end VPVNP
end Computability
end OAI

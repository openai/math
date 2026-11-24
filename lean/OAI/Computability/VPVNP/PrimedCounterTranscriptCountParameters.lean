import OAI.Computability.VPVNP.PrimedCounterTranscriptCount
import OAI.Computability.VPVNP.PrimedCounterResourcesData
import OAI.Computability.VPVNP.RAMApplications

/-!
# One coefficient-counting RAM for all sufficiently large primed pairs

A fixed choice of the address multiplier works simultaneously for the pair
index, exterior header bits, full-degree root and nominated histogram. The
layout is fixed before the header values and histogram are supplied. The
same integer is counted by the native RAM and by the product of its local
validators on the virtual sites.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Resources

open BurstRAM CursorBounds PrimedInputRAM PrimedStackRAM Compression Filter

variable {n r H s w d e : ℕ} {L : Lengths} {Q : Layout L n r H w}

/-- The fitted auxiliary machine and both ways of counting its accepted paths. -/
structure Counts (D : Data Q s) (μ : GrammarDiagonal.Nomination n n (2*r) (Fin s))
    (cap : ProcessorBudget n d e w) : Prop where
  fits : D.Fits
  privateWork : 6 * D.fuel ≤ n^10
  perCall : 15 ≤ 2^e
  total : 15 * D.total ≤ 2^d * 2^e
  native : Nat.card (ActualPaths D.machine.program D.fuel 0 (RAMMemory.initialMemory (2^d) D.initial)
      (withinCaps (2^d) (2^e))) =
    GrammarDiagonal.multiplicity D.degree D.root (PrimedInputRAM.input Q.program Q.fits D.header) μ
  validators : (∑ bits : RawAssignment d e w, ∏ v : Fin (2^d),
      Nat.card (D.machine.IncidentPaths D.fuel 0 (D.initial v) cap.tags cap.capFits v (incidentBits bits v))) =
    GrammarDiagonal.multiplicity D.degree D.root (PrimedInputRAM.input Q.program Q.fits D.header) μ

/-- Uniform Section 11 count at the virtual site and bucket parameters. -/
theorem eventually_counts (p : UniversalMachine.Program) (a d₁ d₂ C B : ℕ)
    (hB : max (max (a+1) (a+d₂)) (max d₁ C) + 2 ≤ B) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2^(n^a-1)), ∀ s, labelCount n n s ≤ n^C →
      let L := PairedChain.lengths (n^a-1) (n^d₂) (n^d₁) i
      let r := addressWidth B n
      let w := CursorBounds.wordBits B n
      ∃ Q : Layout L n r (liveBucket δ n) w, Q.program = p ∧ Q.scratchBase = 2^(virtualBits B n) ∧
        ∃ cap : ProcessorBudget n (virtualBits B n) (roundedUp 1 4 n) w,
          ∀ (degree : Fin n) (root : Fin s) (header : Header L → Bool)
            (μ : GrammarDiagonal.Nomination n n (2*r) (Fin s)), degree.val + 1 = n →
              Counts (Data.ofNomination Q degree root header μ) μ cap := by
  have hpositive : 1 ≤ B := by omega
  filter_upwards [eventually_layouts p a d₁ d₂ C B hB hδ hδ',
    eventually_bothProcessorBudgets hpositive hδ.le hδ'] with n hLayout hCaps
  intro i s hs
  obtain ⟨Q,hp,hbase,hheader,hparams,hbounds⟩ := hLayout i s hs
  refine ⟨Q,hp,hbase,hCaps.2,?_⟩
  intro degree root hdr μ hd
  let D := Data.ofNomination Q degree root hdr μ
  have hf : D.Fits := hbounds.dataFits D hparams hd hheader (fun j => by
    simpa only [D, Data.ofNomination, GrammarDiagonal.exponents_apply] using (μ j).isLt)
  obtain ⟨hwork,hbudget⟩ := hbounds.dataBudget D
  rw [hbase] at hheader
  exact ⟨hf,hwork,hbounds.perCall,hbudget,
    D.transcript_count hf μ rfl _ _ hbounds.perCall hbudget hheader,
    D.incident_count hf μ rfl hbounds.perCall hbudget hheader hCaps.2.tags hCaps.2.capFits⟩

end PrimedCounter.Resources

end VPVNP
end Computability
end OAI

import OAI.Computability.VPVNP.GrammarDiagonal
import OAI.Computability.VPVNP.PrimedCounterData
import OAI.Computability.VPVNP.PrimedInputRAMCapacity

/-!
# Bounded nominations and initial header words

A fixed-width nomination gives one natural exponent for each grammar label.
Its finite-support exponent vector is the monomial tested by the pair counter.
The external-memory initializer supplies its dense word table after the header
bits and uses zero elsewhere.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace GrammarDiagonal

open scoped Classical

variable {n m w : ℕ} {H Site Bits : Type*} [Fintype H]

/-- The monomial indexed by the complete nomination of label counts. -/
noncomputable def exponents (μ : Nomination m n w H) : GrammarLabel (Fin m × Bool) H n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun a => (μ a).val)

@[simp] theorem exponents_apply (μ : Nomination m n w H) (a : GrammarLabel (Fin m × Bool) H n) :
    exponents μ a = (μ a).val := by simp [exponents]

/-- Matching the nominated monomial has precisely the multiplicity of (9.4). -/
theorem coeff_exponents [Fintype Site] [Fintype Bits] (d : Fin n) (h : H) (x : Bits → Site → Fin m → Bool)
    (μ : Nomination m n w H) :
    (PairCoefficient.jointPolynomial d h x).coeff (exponents μ) = (multiplicity d h x μ : ℤ) := by
  rw [PairCoefficient.coeff_eq_count, multiplicity]
  congr 1
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => by
    simp only [DFunLike.ext_iff, exponents_apply])

end GrammarDiagonal

namespace PrimedCounter.Data

open BurstRAM PrimedInputRAM

variable {L : Lengths} {n r H s w b : ℕ} {Q : Layout L n r H w}

/-- Supply every nominated count from its fixed-width field to the parser. -/
noncomputable def ofNomination (Q : Layout L n r H w) (d : Fin n) (root : Fin s)
    (hdr : Header L → Bool) (μ : GrammarDiagonal.Nomination n n b (Fin s)) : Data Q s :=
  ⟨d,root,hdr,GrammarDiagonal.exponents μ⟩

theorem ofNomination_word (d : Fin n) (root : Fin s) (hdr : Header L → Bool)
    (μ : GrammarDiagonal.Nomination n n b (Fin s)) (j : Fin (PrimedStackRAM.labelCount n n s)) :
    (ofNomination Q d root hdr μ).nominatedWord j =
      Fin.ofNat (2^w) (μ ((PrimedStackRAM.labelIndex n n s).symm j)).val := by
  simp [nominatedWord, ofNomination]

/-- Initializing the native validator's memory from the header-provider words
recovers all prescribed histogram components and zeros above the header. -/
theorem initialMemory_eq (D : Data Q s) {S : ℕ} (hfit : Header.count L + D.labels ≤ S) :
    RAMMemory.initialMemory S D.initial = D.initial := by
  apply initialMemory_headerMemory
  simpa only [hist, List.length_ofFn] using hfit

end PrimedCounter.Data

end VPVNP
end Computability
end OAI

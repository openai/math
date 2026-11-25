import OAI.Computability.BorderVNP.PackedHistoryCorrect

/-! # Replacing the dependent tensor-history sum by the checked Boolean profile bits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive VPVNP.VerifierNetwork
open scoped Classical

variable {k b : ℕ} {A : ℕ → Type*} {W G : ℕ → Type}
variable [∀ j, Fintype (W j)] [∀ j, Fintype (G j)] {S : System k b A}
variable {σ R : Type*} [Fintype σ]

/-- Summing over all static profile bit strings with invalid strings contributing zero reproduces
the exact dependent sum, preserving multiplicity of equal output states. -/
theorem sum_transcripts [AddCommMonoid R] (C : Codec S G) (rep : Represents A W) (step : Steps k b W G)
    (correct : LocalCorrect C rep step) (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n)
    (fs : Leaves k (Frame σ (W 0)) n) (x : σ → Bool) (hl : LeafState rep x n a fs)
    (readout : (W n → Bool) → R) (value : A n → R) (hr : ∀ z s, rep n z s → readout z = value s) :
    (∑ g : Slot k G n → Bool, if flag step n hn fs x g then readout (output step n hn fs x g) else 0) =
      ∑ q : (S.histories n hn a).Index, value (state n hn a q) := by
  classical
  let acc := fun g : Slot k G n → Bool => flag step n hn fs x g = true
  let y := fun g : Slot k G n → Bool => readout (output step n hn fs x g)
  change (∑ g : Slot k G n → Bool, if acc g then y g else 0) = _
  have sumA : (∑ g : Slot k G n → Bool, if acc g then y g else 0) = ∑ z : {g // acc g}, y z.val := by
    rw [← Finset.sum_filter, Finset.sum_subtype (p := acc) _ (fun _ => by simp) y]
  rw [sumA, ← (acceptedEquiv C rep step correct n hn a fs x hl).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  change readout (output step n hn fs x (encode C n hn a q)) = _
  exact hr _ _ ((semantics C rep step correct n hn a fs x hl _).2 q rfl)

variable {D : ℕ} {P : Type} {bits : P → ℕ}

/-- Exact physical contraction after replacing every dependent profile choice by the public
static bits accepted by the compiled Boolean history verifier. -/
theorem tensor_transcripts [CommSemiring R] (C : Codec S G) (rep : Represents A W) (step : Steps k b W G)
    (correct : LocalCorrect C rep step) (pack : ∀ j, A j → Shortening.Pack D (Port k P j) (width bits k j) R)
    (exact : S.Exact pack) (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n)
    (fs : Leaves k (Frame σ (W 0)) n) (x : σ → Bool) (hl : LeafState rep x n a fs)
    (ports : Crossing.Ports (width bits k n)) (readout : (W n → Bool) → R)
    (hr : ∀ z s, rep n z s → readout z = (pack n s).tensor ports) :
    (parallelLeaves (pack 0) n a).tensor ports =
      ∑ g : Slot k G n → Bool, if flag step n hn fs x g then readout (output step n hn fs x g) else 0 := by
  rw [sum_transcripts C rep step correct n hn a fs x hl readout _ hr]
  exact S.tensor_histories pack exact n hn a ports

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI

import OAI.Computability.BorderVNP.ResidueEntryScalar
import OAI.Computability.BorderVNP.ResidueEntryReaderExtension

/-! # A single polynomial-size entry reader for all field coefficients

The word-bank interpretation here is the additive prime-field basis encoding, with one
word per coefficient. The sum ranges over actual binary guesses. It therefore supplies
the arbitrary-scalar computation in Lemma 10.1 independently of the multiplicative
gadget encoding needed later for §11.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryVerifier

open VPVNP ExactQuantumFactoring Module ResidueEntryBudget ResidueEntryInput
open ResidueFourier ResiduePins ResidueBox ResidueIndex ResidueEntryOutput
open ResidueEntryVerifierCore ResidueEntryField
open scoped BigOperators Classical

/-- A single shared bounded Boolean circuit for all arbitrary scalar queries at the
given scale, with canonical additive basis coordinates and an exact prime-field count. -/
def ScalarEntryReader {σ ι E : Type*} [Fintype σ] [Fintype ι] [Field E] [Fintype E]
    {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) E] {D : ℕ} (BE : Basis (Fin D) (ZMod p) E)
    (q : ℕ) (hq : 0 < q) (H s : ℕ) (g : ι → MvPolynomial (Option σ) E) : Prop :=
    let width := (q-1) * ∑ t, (g t).totalDegree
    let idx := workWidth q H width
    let h := Fintype.card (Option σ)
    let b := Nat.clog 2 p
    let w := b+1
    ∃ N ≤ Fintype.card E * (width+1), width < N-1 ∧
      ∃ d, D ≤ Nat.clog 2 N ∧ d ≤ Nat.clog 2 N ∧ p ≤ N ∧
      ∃ circuit : BooleanNetwork (Fintype.card (Input σ idx D (Fin D) b d w b)) 1,
        circuit.net.count ≤ jointBudget h idx D d w D b
          (entryGateBudget (Fintype.card ι) h s (q-1).size (N-1-1).size idx + D*(2*b+2)+1) ∧
        ∀ (a : E) (μ : Exponent σ), Fits H μ → ∀ i j : Index (Fin D) σ H,
          (∑ guess : Guess σ d w b → Bool, if circuit.eval (number (Sum.elim
            (encodeQuery idx H b i.2.val μ j.2.val i.1 j.1 (fun l => (BE.coord l a).val)) guess)) 0
            then (1 : ZMod p) else 0) = weights BE H q hq g (.id E) μ a i j

/-- The concrete arbitrary-scalar reader on the bounded interpolation extension.
Both the field and the Boolean network are fixed before the coefficient, monomial
and two pin indices are supplied. -/
theorem exists_scalar_reader {σ ι E : Type*} [Fintype σ] [Fintype ι] [Field E] [Fintype E]
    (p : ℕ) [Fact p.Prime] [CharP E p] [Algebra (ZMod p) E] {D : ℕ}
    (BE : Basis (Fin D) (ZMod p) E) (q H s : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option σ) E) (hg : ∀ t, circuitSize (g t) ≤ s) :
    ScalarEntryReader BE q hq H s g := by
  unfold ScalarEntryReader
  intro width idx h b w
  obtain ⟨K, hK, hfin, hAlgebra, φ, d, BK, hfield, hcard, hD, hd, hpN⟩ :=
    exists_bounded_grid_basis p BE width
  let N := Fintype.card K
  have hsize : Fintype.card Kˣ = N-1 := Fintype.card_units K
  have hp : p < 2^w := (dimensions_le BK (Nat.le_pow_clog Nat.one_lt_two N)).2.2
  choose π hπ using fun j => exists_coordinate_extension p φ (BE.coord j)
  obtain ⟨k, hk, C, hc⟩ := exists_scalar_dag BE φ.toRingHom q H width idx s b hq
    (Nat.le_pow_clog Nat.one_lt_two p) (workWidth_fit q H width) g rfl hg
  let F := verifier BK hp C (fieldNet (b := b) q H width BK (φ ∘ BE)) (valid p) yNet (project w BK π)
  have budget := joint_count (b := b) q H width BK hp C (φ ∘ BE) π
  rw [Fintype.card_fin] at budget
  rw [hsize] at hk
  refine ⟨N, hcard, hsize ▸ hfield, d, hD, hd, hpN, F, budget.trans (jointBudget_mono_dag h idx D d w D b hk), ?_⟩
  intro a μ hm i j
  have h := counted_scalar BE BK φ π hπ hp q H width hq g hfield a C i j μ
    (fun l => (BE.coord l a).val) (fun x => hc a (BE i.1) i.2.val μ j.2.val
      (fits_of_inBox i.2.property) hm (fits_of_inBox j.2.property) x)
  simpa only [build, Transcript.circuit_eval] using h

end ResidueEntryVerifier

end BorderVNP
end Computability
end OAI

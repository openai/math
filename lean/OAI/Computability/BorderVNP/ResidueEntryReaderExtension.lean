import OAI.Computability.BorderVNP.ResidueEntryVerifier
import OAI.Computability.BorderVNP.ResidueEntryBudgetFamily

/-! # Choosing a small interpolation field for the common binary entry reader

The circuit uses one field extension for the whole matrix family. Its order is at most
the ground-field order times one more than the width of the interpolation interval.
Only the bit length of this order enters the Boolean circuit and advice bounds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryVerifier

open ExactQuantumFactoring Module ResidueFourier ResidueBox ResiduePins
open ResidueEntryInput ResidueEntryBudget ResidueIndex VPVNP
open scoped BigOperators Classical

universe u

private theorem gridField (E : Type u) [Field E] [Fintype E] (width : ℕ) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : E →+* K),
      width < Nat.card Kˣ ∧ Nat.card K ≤ Fintype.card E * (width + 1) := by
  obtain ⟨K, hfinite, hw, hcard⟩ := exists_interpolation_field E width
  let _ : Fintype K := Fintype.ofFinite K
  exact ⟨↥K, inferInstance, inferInstance, algebraMap E K, hw, hcard⟩

private noncomputable def gridBasis (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod p) K] : Basis (Fin (Module.finrank (ZMod p) K)) (ZMod p) K :=
  Module.finBasis _ _

/-- A bounded interpolation field with a numbered prime-field basis. This same field
can serve either the arbitrary scalar encoding or the gadget-product encoding. -/
theorem exists_bounded_grid_basis {E : Type u} [Field E] [Fintype E] (p : ℕ) [Fact p.Prime]
    [CharP E p] [Algebra (ZMod p) E] {D : ℕ} (BE : Basis (Fin D) (ZMod p) E) (width : ℕ) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : Algebra (ZMod p) K),
      ∃ (_ : E →ₐ[ZMod p] K) (d : ℕ) (_ : Basis (Fin d) (ZMod p) K),
      width < Fintype.card Kˣ ∧ Fintype.card K ≤ Fintype.card E * (width+1) ∧
      D ≤ Nat.clog 2 (Fintype.card K) ∧ d ≤ Nat.clog 2 (Fintype.card K) ∧ p ≤ Fintype.card K := by
  obtain ⟨K, hK, hfinite, ιK, hwidth', hcard⟩ := gridField E width
  rw [Nat.card_eq_fintype_card] at hwidth' hcard
  let _ : CharP K p := charP_of_injective_ringHom ιK.injective p
  let _ : Algebra (ZMod p) K := ZMod.algebra _ _
  let φ : E →ₐ[ZMod p] K := { ιK with
    commutes' := DFunLike.congr_fun (RingHom.ext_zmod (ιK.comp (algebraMap _ _)) _) }
  let BK := gridBasis p K
  exact ⟨K, hK, hfinite, inferInstance, φ, _, BK, hwidth', hcard, field_dimensions φ.toRingHom BE BK⟩

/-- A common polynomially bounded binary reader for the multiplicative gadget query
at one scale, with explicit interpolation-field and bit-width bounds. -/
def GadgetEntryReader {σ ι J E : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Field E] [Fintype E]
    {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) E] {D : ℕ} (BE : Basis (Fin D) (ZMod p) E)
    (q : ℕ) (hq : 0 < q) (H s : ℕ) (g : ι → MvPolynomial (Option σ) E)
    (m : ℕ) (gadgets : J → E) : Prop :=
    let width := (q-1) * ∑ t, (g t).totalDegree
    let idx := workWidth q H width
    let h := Fintype.card (Option σ)
    let b := Nat.clog 2 p
    let w := b+1
    ∃ N ≤ Fintype.card E * (width+1), width < N-1 ∧
      ∃ d, D ≤ Nat.clog 2 N ∧ d ≤ Nat.clog 2 N ∧ p ≤ N ∧
      ∃ circuit : BooleanNetwork (Fintype.card (Input σ idx D J m d w b)) 1,
        circuit.net.count ≤ jointBudget h idx D d w (Fintype.card J) m
          (gadgetBudget (Fintype.card ι) h s (q-1).size (N-1-1).size idx (Fintype.card J) m) ∧
        ∀ (i j : Index (Fin D) σ H) (μ : Exponent σ), Fits H μ →
        ∀ δ : J → ℕ, (∀ l, δ l < 2^m) →
          (∑ guess : Guess σ d w b → Bool, if circuit.eval (number (Sum.elim
            (encodeQuery idx H m i.2.val μ j.2.val i.1 j.1 δ) guess)) 0 then
              (1 : ZMod p) else 0) =
          weights BE H q hq g (.id E) μ (∏ l, gadgets l ^ δ l) i j

/-- Choose the actual interpolation extension, the limb basis and the common reader
before all basis and box indices. The resulting AND/NOT network has a resource bound
depending only on ground-field, degree, width and circuit-size parameters. -/
theorem exists_reader_over_base {σ ι J E : Type*} [Fintype σ] [Fintype ι] [Fintype J]
    [Field E] [Fintype E] (p : ℕ) [Fact p.Prime] [CharP E p] [Algebra (ZMod p) E]
    {D : ℕ} (BE : Basis (Fin D) (ZMod p) E) (q H s m : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option σ) E) (hg : ∀ t, circuitSize (g t) ≤ s) (gadgets : J → E) :
    GadgetEntryReader BE q hq H s g m gadgets := by
  unfold GadgetEntryReader
  intro width idx h b w
  obtain ⟨K, hK, hfinite, hAlgebra, φ, d, BK, hwidth', hcard, hD, hd, hpN⟩ :=
    exists_bounded_grid_basis p BE width
  let N := Fintype.card K
  have hsize : Fintype.card Kˣ = N-1 := Fintype.card_units K
  have hp : p < 2^w := (ResidueEntryField.dimensions_le BK (Nat.le_pow_clog Nat.one_lt_two N)).2.2
  obtain ⟨c, hc, hcount⟩ := exists_reader_network (m := m) BE BK φ hp q H width s hq
    (workWidth_fit q H width) g rfl hwidth' hg gadgets
  refine ⟨N, hcard, hsize ▸ hwidth', _, hD, hd, hpN, c, ?_, hcount⟩
  rw [← hsize]; exact hc

end ResidueEntryVerifier

end BorderVNP
end Computability
end OAI

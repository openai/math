import OAI.Computability.BorderVNP.ResidueEntryOutput
import OAI.Computability.BorderVNP.ResidueEntryVerifierCore

/-! # Acceptance of the binary residue-entry verifier on every raw guess -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryOutput

open ExactQuantumFactoring BooleanNetwork BitArithmetic VPVNP
open ResidueEntryInput ResidueEntryField ResidueEntryVerifierCore ResidueFourier ResidueBox
open scoped Classical

variable {σ J ι E K : Type*} [Fintype σ] [Fintype J] [Fintype ι]
  [Field E] [Field K] [Fintype K] {idx D m d w b p gates : ℕ}
  [Fact p.Prime] [Algebra (ZMod p) K]

/-- For fixed query data and arbitrary binary guesses, the common verifier
accepts exactly when the final word is below the projected interpolation
summand. Out-of-range limbs and zero grid points give value zero. -/
theorem build_eval_scalar (hp : p < 2^w) (hb : b ≤ w) (B : Module.Basis (Fin d) (ZMod p) K)
    (φ : E →+* K) (basis : Fin D → E) (π : Fin D → K →ₗ[ZMod p] ZMod p)
    (C : Circuit K (GadgetInput σ idx J m) gates) (q H width : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (a : E)
    (e μ k : Exponent σ) (row col : Fin D) (δ : J → ℕ)
    (hc : ∀ x : Option σ → Kˣ, C.eval id
        (Sum.elim (queryAssignment q H width idx x (ResidueIndex.encode idx H e μ k) 1 (φ (basis row)))
          (fun (j,i) => if (δ j).testBit i.val then 1 else 0)) =
        pathSummand φ q g a (basis row) e μ k x)
    (grid : Option σ → Fin (d*w) → Bool) (y : Fin b → Bool) :
    (build B hp C (fieldNet q H width B (φ ∘ basis)) (valid p) yNet (project w B π)).eval
        (number (Sum.elim (encodeQuery idx H m e μ k row col δ) (encodeGuess grid y))) = true ↔
      value y < (packedValue B (fun x => π col
        (pathSummand φ q g a (basis row) e μ k x))
        (fun i => limbWords d w (grid i))).val := by
  let query := encodeQuery idx H m e μ k row col δ
  let raw := number (Sum.elim query (encodeGuess grid y))
  let inputs := fieldNet (σ := σ) (idx := idx) (J := J) (m := m) (w := w) (b := b) q H width B (φ ∘ basis)
  let C' := build B hp C inputs (valid p) yNet (project w B π)
  let f (x : Option σ → Kˣ) : GadgetInput σ idx J m → K := Sum.elim
    (queryAssignment q H width idx x (ResidueIndex.encode idx H e μ k) 1 (φ (basis row)))
    (fun (j,i) => if (δ j).testBit i.val then (1 : K) else 0)
  let R (x : Option σ → Kˣ) := pathSummand φ q g a (basis row) e μ k x
  let limbs (i : Option σ) := limbWords d w (grid i)
  have guard := valid_eval hp query grid y
  have hg (hv : ∀ i, validLimbs p (limbs i)) (x : Option σ → Kˣ)
      (hx : ∀ i, (x i : K) = unpackScalar B (limbs i)) :
      C'.eval raw = true ↔ value y < (π col (R x)).val := by
    have hh := build_eval B hp hb C inputs (valid p) yNet (project w B π) raw (f x) (π col (R x))
      (fun _ => fieldNet_represents_valid q H width hp B (φ ∘ basis) e μ k row col δ grid y x hv hx)
      (fun _ z hz => (project_eval hp B π H e μ k row col δ grid y z _ hz).trans
        (congrArg (fun a => (π col a).val) (hc x)))
    rw [yNet_eval query grid y] at hh
    exact hh.trans (and_iff_right (guard.mpr hv))
  change C'.eval raw = true ↔ value y < (packedValue B (fun x => π col (R x)) limbs).val
  rw [packedValue]
  split
  next hv => exact hg hv _ (fun _ => rfl)
  next hv =>
    have h := build_eval B hp hb C inputs (valid p) yNet (project w B π) raw
      (fun _ => 0) 0 (fun ok => (hv (guard.mp ok)).elim) (fun ok => (hv (guard.mp ok)).elim)
    exact h.trans (by simp)

/-- Specialization to the product of gadget values specified by their multiplicity words. -/
theorem build_eval_packed (hp : p < 2^w) (hb : b ≤ w) (B : Module.Basis (Fin d) (ZMod p) K)
    (φ : E →+* K) (basis : Fin D → E) (π : Fin D → K →ₗ[ZMod p] ZMod p)
    (C : Circuit K (GadgetInput σ idx J m) gates) (q H width : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (gadgets : J → E)
    (e μ k : Exponent σ) (row col : Fin D) (δ : J → ℕ)
    (hc : ∀ x : Option σ → Kˣ, C.eval id
        (Sum.elim (queryAssignment q H width idx x (ResidueIndex.encode idx H e μ k) 1 (φ (basis row)))
          (fun (j,i) => if (δ j).testBit i.val then 1 else 0)) =
        pathSummand φ q g (∏ j, gadgets j^δ j) (basis row) e μ k x)
    (grid : Option σ → Fin (d*w) → Bool) (y : Fin b → Bool) :
    (build B hp C (fieldNet q H width B (φ ∘ basis)) (valid p) yNet (project w B π)).eval
        (number (Sum.elim (encodeQuery idx H m e μ k row col δ) (encodeGuess grid y))) = true ↔
      value y < (packedValue B (fun x => π col
        (pathSummand φ q g (∏ j, gadgets j^δ j) (basis row) e μ k x))
        (fun i => limbWords d w (grid i))).val :=
  build_eval_scalar hp hb B φ basis π C q H width g (∏ j, gadgets j^δ j) e μ k row col δ hc grid y

end ResidueEntryOutput

end BorderVNP
end Computability
end OAI

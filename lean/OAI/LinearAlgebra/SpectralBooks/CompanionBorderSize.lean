import OAI.LinearAlgebra.SpectralBooks.BorderCharacteristic
import OAI.Computability.BorderVNP.ModelGroundImage
import OAI.Computability.BorderVNP.ModelGateExtension

/-! # Transfer of the companion degree-component circuit lower bound -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial OAI.Computability.BorderVNP.Homogenize

variable {F σ : Type*} [Field F]

/-- One shared gate list makes every original register available. Scalar and
variable registers are free references in the companion model. -/
private theorem companion_program_wires {r : ℕ} (p : Program F σ r) :
    ∃ q : OAI.Computability.VPVNP.Program F σ p.cost, ∀ i, HasWire q (registerPolynomial p i) := by
  induction p with
  | nil => exact ⟨.nil, fun i => i.elim0⟩
  | @step r p gate ih =>
    obtain ⟨q, wires⟩ := ih
    cases gate with
    | constant a => exact ⟨q, Fin.cases (hasWire_const q a) wires⟩
    | input x => exact ⟨q, Fin.cases (hasWire_var q x) wires⟩
    | add a b =>
      obtain ⟨q', old, new⟩ := append_binary q .add (wires a) (wires b)
      exact ⟨q', Fin.cases new (fun i => old _ (wires i))⟩
    | sub a b =>
      obtain ⟨q', old, new⟩ := append_binary q .sub (wires a) (wires b)
      exact ⟨q', Fin.cases new (fun i => old _ (wires i))⟩
    | mul a b =>
      obtain ⟨q', old, new⟩ := append_binary q .mul (wires a) (wires b)
      exact ⟨q', Fin.cases new (fun i => old _ (wires i))⟩

private theorem circuitCoefficientVectors_subset_companion (d s : ℕ) :
    circuitCoefficientVectors F σ d s ⊆ OAI.Computability.BorderVNP.circuitImage F σ d s := by
  rintro _ ⟨r, p, o, bound, rfl⟩
  obtain ⟨q, available⟩ := companion_program_wires p
  obtain ⟨wire, hwire⟩ := available o
  exact ⟨p.cost, bound, ⟨q,wire⟩, congrArg (OAI.Computability.BorderVNP.coeffVector d) hwire⟩

/-- Over an arbitrary field, a degree-component circuit approximation transfers
to the companion geometric model at the identical gate count and degree. -/
theorem companion_borderSize_le_degreeBorderSize (d : ℕ) (f : MvPolynomial σ F) :
    OAI.Computability.BorderVNP.borderSize d f ≤ degreeBorderSize d f := by
  apply OAI.Computability.BorderVNP.borderSize_le_iff.mpr
  exact OAI.Computability.BorderVNP.imageClosure_mono (circuitCoefficientVectors_subset_companion d _)
    ((degreeBorderSize_le_iff d _ f).mp le_rfl)

/-- The same comparison holds for the actual ground-field circuit image over
an infinite field. -/
theorem companion_groundBorderSize_le_degreeBorderSize [Infinite F] (d : ℕ) (f : MvPolynomial σ F) :
    OAI.Computability.BorderVNP.groundBorderSize d f ≤ degreeBorderSize d f := by
  rw [← OAI.Computability.BorderVNP.borderSize_eq_groundBorderSize]
  exact companion_borderSize_le_degreeBorderSize d f

/-- The companion's ground-field size bound on an infinite field gives the
same degree-component lower bound with no loss in its real threshold. -/
theorem degreeBorderSizeAtLeast_of_companion_ground [Infinite F]
    (d : ℕ) (b : ℝ) (f : MvPolynomial σ F) (lower : b ≤ (OAI.Computability.BorderVNP.groundBorderSize d f : ℝ)) :
    DegreeBorderSizeAtLeast d b f :=
  lower.trans (Nat.cast_le.mpr (companion_groundBorderSize_le_degreeBorderSize d f))

/-- A prime-field algebraic-closure bound on an integral polynomial works over
every field of that characteristic, including finite fields. -/
theorem degreeBorderSizeAtLeast_intCast_of_companion {K : Type*} [Field K]
    (p d : ℕ) [CharP K p] [CharP F p] (b : ℝ) (f : MvPolynomial σ ℤ)
    (lower : b ≤ (OAI.Computability.BorderVNP.groundBorderSize d (map (Int.castRingHom (AlgebraicClosure K)) f) : ℝ)) :
    DegreeBorderSizeAtLeast d b (map (Int.castRingHom F) f) := by
  have atClosure := degreeBorderSizeAtLeast_of_companion_ground d b _ lower
  unfold DegreeBorderSizeAtLeast at atClosure ⊢
  rw [degreeBorderSize_eq_of_charP F (AlgebraicClosure K) p d f]
  exact atClosure

/-- A degree-by-length profile bound has the same threshold lengths and
exponent after changing to the native circuit model and coefficient field. -/
theorem eventually_degreeBorderSizeAtLeast_intCast_of_companion
    {K : Type*} [Field K] (p : ℕ) [CharP K p] [CharP F p]
    {ι : ℕ → Type*} (f : ∀ n, MvPolynomial (ι n) ℤ) (bound : ℕ → ℝ)
    (lower : ∀ᶠ n in Filter.atTop, bound n ≤
      (OAI.Computability.BorderVNP.groundBorderSize n (map (Int.castRingHom (AlgebraicClosure K)) (f n)) : ℝ)) :
    ∀ᶠ n in Filter.atTop, DegreeBorderSizeAtLeast n (bound n) (map (Int.castRingHom F) (f n)) :=
  lower.mono fun n hn => degreeBorderSizeAtLeast_intCast_of_companion p n (bound n) (f n) hn

end SpectralBooks
end LinearAlgebra
end OAI

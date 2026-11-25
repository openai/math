import OAI.LinearAlgebra.FiniteFourier.ConvolutionJet

/-! # Circuit for sparse packing and quadratic projections of a jet

Each packed coefficient reads at most one array cell. Fill all other positions
with zero, then form the three common projection rows for the variable-operand
convolutions.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped Classical

noncomputable section
variable {R : Type*} [CommRing R] {e h : ℕ}

private def jetIndex (i : Fin h × Fin e) : ℕ := i.1.val * (2*e-1) + i.2.val

private theorem jetIndex_injective : Function.Injective (jetIndex (e := e) (h := h)) := by
  intro i j hij
  let s := 2*e-1
  have hi : i.2.val < s := by have := i.2.isLt; dsimp [s]; omega
  have hj : j.2.val < s := by have := j.2.isLt; dsimp [s]; omega
  change i.1.val*s + i.2.val = j.1.val*s + j.2.val at hij
  have hmod := congrArg (· % s) hij
  simp [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  rw [hmod] at hij
  have hmul := Nat.add_right_cancel hij
  exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt hi) hmul)) (Fin.ext hmod)

/-- Both coordinates of every packed coefficient are available as free readouts. -/
def jetPackingCircuit (R : Type*) [CommRing R] (e h : ℕ) :
    Circuit R ((Fin h × Fin e) × Fin 2) (Σ _ : Fin (2*e*h), Fin 2) 0 where
  program := .nil
  output k := if hk : ∃ i : Fin h × Fin e, jetIndex i = k.1.val then
    .scaled 1 (.inl (hk.choose, k.2)) else .zero

theorem jetPackingCircuit_eval (x : (Fin h × Fin e) × Fin 2 → R)
    (k : Fin (2*e*h)) (j : Fin 2) :
    (jetPackingCircuit R e h).eval x ⟨k,j⟩ = (jetPack (fun i => x (i,j))).coeff k := by
  simp only [Circuit.eval, jetPackingCircuit, jetPack, finsetSum_coeff, coeff_monomial]
  change (if hk : ∃ i : Fin h × Fin e, jetIndex i = k.val then
      Readout.scaled 1 (Sum.inl (hk.choose, j)) else Readout.zero).eval _ =
    ∑ i : Fin h × Fin e, if jetIndex i = k.val then x (i,j) else 0
  split_ifs with hk
  · rw [Finset.sum_eq_single hk.choose]
    · simp [hk.choose_spec, Readout.eval]
    · intro b _ hb
      simp [show jetIndex b ≠ k.val from fun H => hb (jetIndex_injective (H.trans hk.choose_spec.symm))]
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro b _
    simp [show jetIndex b ≠ k.val from fun H => hk ⟨b,H⟩]

/-- Starting from the two scalar entries of each jet cell, one copy of the
base-ring encoder supplies every child with exactly its required input vector. -/
theorem exists_jetChildInput_circuit (R : Type*) [CommRing R] (e h : ℕ) :
    ∃ u ≤ 2*e*h, ∃ enc : Circuit R ((Fin h × Fin e) × Fin 2) (Σ _ : Fin (2*e*h), Fin 3) u,
      ∀ x (k : Fin (2*e*h)) (j : Fin 3), enc.eval x ⟨k,j⟩ =
        jetChildInput (fun i => x (i,0)) (fun i => x (i,1)) j k := by
  obtain ⟨_, _, q, _, hq, _, heval, _⟩ :=
    exists_quadratic_convolution_circuits (0 : R) 0 (2*e*h)
  obtain ⟨u, hu, enc, henc⟩ := circuit_comp (jetPackingCircuit R e h) q
  refine ⟨u, by omega, enc, fun x k j => ?_⟩
  rw [henc, heval, jetPackingCircuit_eval, jetPackingCircuit_eval]
  rfl

end

end FiniteFourier
end LinearAlgebra
end OAI

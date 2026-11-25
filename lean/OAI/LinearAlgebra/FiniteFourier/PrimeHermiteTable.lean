import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteLocal
import OAI.LinearAlgebra.FiniteFourier.PrimeRepairProgram
import Mathlib.LinearAlgebra.Pi

/-! # Compiling the spectral repair table

On each of the two blocks of check rows, the ordinary-to-spectral change
of coordinates is paid once in each direction. The table between the two
conversions acts independently at every spectral label.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K I O : Type*} [Fintype I]

/-- Run the same circuit on independent rows, with the row index first. -/
theorem RealizesOp.rows [CommSemiring K] (B : Type*) [Fintype B] {F : (I → K) → O → K} {c : ℕ}
    (hF : RealizesOp F c) :
    RealizesOp (fun (x : B × I → K) (p : B × O) => F (fun i => x (p.1, i)) p.2)
      (Fintype.card B * c) := by
  have h := realizesOp_pointwise (fun _ : B => hF)
  simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, Function.comp_def,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap] using
    h.reindex (Equiv.prodComm I B) (Equiv.prodComm O B)

/-- The two blocks of `s` check rows each undergo one forward and one inverse
spectral conversion. The middle table costs at most `(2*s)^2` gates per label. -/
theorem realizesOp_ordinaryRepairTable [CommRing K] {ν : Type*} [Fintype ν] {s f g : ℕ}
    (S : (I → K) ≃ₗ[K] (ν → K))
    (T : ν → ((Fin s → K) × (Fin s → K)) →ₗ[K] ((Fin s → K) × (Fin s → K)))
    (hf : RealizesOp S f) (hg : RealizesOp S.symm g) :
    RealizesOp (fun (x : (Fin s ⊕ Fin s) × I → K) (p : (Fin s ⊕ Fin s) × I) =>
      let t := ordinaryRepairTable S T (fun i a => x (.inl i, a)) (fun i a => x (.inr i, a))
      Sum.elim t.1 t.2 p.1 p.2)
      (2*s*f + Fintype.card ν * (2*s)^2 + 2*s*g) := by
  let B := Fin s ⊕ Fin s
  let e := LinearEquiv.sumArrowLequivProdArrow (Fin s) (Fin s) K K
  let L (v : ν) : (B → K) →ₗ[K] (B → K) := e.symm.toLinearMap.comp ((T v).comp e.toLinearMap)
  have h := (hg.rows B).comp ((realizesOp_pointwise_linear L).comp (hf.rows B))
  convert h using 1
  · funext x ⟨i, a⟩
    cases i <;> rfl
  · simp [B]
    ring

end FiniteFourier
end LinearAlgebra
end OAI

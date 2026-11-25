import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyMatrix
import Mathlib.Data.Matrix.Block

/-! # Reindexing jet circuits and discarding borrowed workspace -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
variable {φ : R →+* S} {η : S} {m : S[X]} {e h : ℕ} {C : ℝ}

/-- Relabel the input jet blocks and select output jet blocks at the same gate count. -/
theorem JetMatrixCircuit.reindex {I I' O O' : Type*} [Fintype I] [Fintype I']
    {A : Matrix O I (JetQuotient m h)} (hc : JetMatrixCircuit φ η m e h A C)
    (eo : O' → O) (ei : I' ≃ I) :
    JetMatrixCircuit φ η m e h (A.submatrix eo ei) C := by
  obtain ⟨g, hg, q, hq⟩ := hc
  let p := q.rewire (fun i => (1, (ei.symm i.1, i.2)))
    (fun o : O' × ((Fin h × Fin e) × Fin 2) => (1, (eo o.1, o.2)))
  refine ⟨g, hg, p, fun x => ?_⟩
  rw [submatrix_mulVec_equiv]
  have hx : jetOperandArray φ η m (fun i => x (ei.symm i.1, i.2)) =
      jetOperandArray φ η m x ∘ ei.symm := rfl
  funext o
  have heval := congrFun (hq (fun i => x (ei.symm i.1, i.2))) (eo o)
  rw [hx] at heval
  simpa only [jetOperandArray, p, Circuit.eval_rewire, one_mul, Function.comp_apply] using heval

/-- Discard an identity workspace attached to a rectangular jet action. -/
theorem JetMatrixCircuit.eliminateWorkspace {I O W : Type*} [Fintype I] [Fintype W] [DecidableEq W]
    {A : Matrix O I (JetQuotient m h)}
    (hc : JetMatrixCircuit φ η m e h (fromBlocks A 0 0 (1 : Matrix W W _)) C) :
    JetMatrixCircuit φ η m e h A C := by
  obtain ⟨g, hg, q, hq⟩ := hc
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let p : Circuit R (I × ((Fin h × Fin e) × Fin 2)) (O × ((Fin h × Fin e) × Fin 2)) 0 :=
      ⟨.nil, fun _ => .zero⟩
    refine ⟨0, by simpa using (Nat.cast_nonneg g).trans hg, p, fun x => ?_⟩
    funext o
    simp [p, jetOperandArray, jetOperandValue, jetQuotientValue, jetBivariate,
      quadraticJetArray, Circuit.eval, Readout.eval, mulVec, dotProduct]
  | inr hI =>
    let pick : I ⊕ W → I := Sum.elim id (fun _ => hI.some)
    let p := q.rewire (fun i => (1, (pick i.1, i.2)))
      (fun o : O × ((Fin h × Fin e) × Fin 2) => (1, (Sum.inl o.1, o.2)))
    refine ⟨g, hg, p, fun x => ?_⟩
    have hw := hq (fun i => x (pick i.1, i.2))
    rw [fromBlocks_mulVec] at hw
    have hx : jetOperandArray φ η m (fun i => x (pick i.1, i.2)) ∘ Sum.inl =
        jetOperandArray φ η m x := rfl
    rw [hx] at hw
    funext o
    simpa only [jetOperandArray, p, Circuit.eval_rewire, one_mul, zero_mulVec,
      add_zero, Sum.elim_inl, Function.comp_apply, pick, id_eq] using congrFun hw (Sum.inl o)

end FiniteFourier
end LinearAlgebra
end OAI

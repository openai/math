import OAI.LinearAlgebra.SpectralBooks.PortGraph.BoundedPatchReplacementClosure
import OAI.LinearAlgebra.SpectralBooks.BoundedPatchReplacementMaps

/-! # Direct replacement of a bounded patch with at most three stubs

The open tensor itself is a single vertex table with the prescribed boundary
ports and no internal wires. A single arithmetic program computes its whole table.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

section

open PlanarPatch Arithmetic

private theorem prod_inputs {F I V : Type*} [Field F] [Fintype V]
    (p : V → MvPolynomial I F) (hp : ∀ v, HasFormula 1 (p v)) :
    HasFormula (Fintype.card V + 1) (∏ v, p v) := by
  have h (s : Finset V) : HasFormula (s.card + 1) (∏ v ∈ s, p v) := by
    induction s using Finset.induction_on with
    | empty => simpa using HasFormula.const (I := I) (1 : F)
    | insert a s ha ih =>
      simpa [ha, Nat.add_comm, Nat.add_left_comm] using (hp a).mul ih
  simpa using h Finset.univ

/-- Formula weight for a single entry of the direct contraction. -/
theorem PortGraph.small_stub_formula {V E B F I : Type*} [Fintype V] [Fintype E] [Field F]
    (G : PortGraph V E) (attach : B → V) (q : ℕ)
    (U : G.StubTable attach (Fin q) (MvPolynomial I F)) (hU : ∀ v a s, HasFormula 1 (U v a s))
    (x : B → Fin q) :
    HasFormula ((Fintype.card (E → Fin q) + 1) * (Fintype.card V + 1)) (G.openValue attach U x) :=
  HasFormula.fintypeSum (by omega) (fun y => prod_inputs _ (fun v => hU v _ _))

/-- When there are at most three stubs, the single table produced by direct contraction
is a tree of maximum degree three. The program takes the original entries as inputs. -/
theorem PortGraph.small_stub_program {V E B F I : Type*} [Fintype V] [Fintype E] [Fintype B]
    [Field F] (G : PortGraph V E) (attach : B → V) {K w : ℕ} (hK : Fintype.card V ≤ K)
    (hdeg : ∀ v, Fintype.card (G.Port v) + Fintype.card {b // attach b = v} ≤ 4)
    (hsmall : Fintype.card B ≤ 3)
    (U : G.StubTable attach (Fin (2^w)) (MvPolynomial I F)) (hU : ∀ v a s, HasFormula 1 (U v a s)) :
    ∃ (r : ℕ) (p : Program F I r) (out : (B → Fin (2^w)) → Fin r),
      (∀ x, registerPolynomial p (out x) = G.openValue attach U x) ∧
      p.cost ≤ 2^((5*K+5)*(w+1)) := by
  have he : Fintype.card E ≤ 4*K := by
    have h := (G.closed_size_bounds attach hK hdeg).2
    rw [Fintype.card_sum] at h
    omega
  have hf (x : B → Fin (2^w)) : HasFormula
      ((Fintype.card (E → Fin (2^w)) + 1) * (Fintype.card V + 1)) (G.openValue attach U x) := by
    exact G.small_stub_formula attach _ U hU x
  choose e hval hcost using hf
  let p := Expression.compileFamily e
  refine ⟨p.registers, p.program, p.output, fun x => (registerPolynomial_compileFamily e x).trans
    (hval x),?_⟩
  rw [p.cost_eq]
  calc
    _ ≤ ∑ _ : B → Fin (2^w), (Fintype.card (E → Fin (2^w)) + 1) * (Fintype.card V + 1) :=
      Finset.sum_le_sum (fun x _ => (Nat.le_succ _).trans (hcost x))
    _ = (2^w)^Fintype.card B * (((2^w)^Fintype.card E + 1) * (Fintype.card V+1)) := by simp
    _ ≤ (2^w)^3 * (((2^w)^(4*K) + 1) * (K+1)) := by gcongr
    _ ≤ 2^(w*3) * (2^(w*(4*K)+1) * 2^(K+1)) := by
      rw [← pow_mul, ← pow_mul, pow_succ 2 (w*(4*K))]
      gcongr
      · have := Nat.one_le_pow (w*(4*K)) 2 (by decide); omega
      · exact Nat.lt_two_pow_self.le
    _ ≤ _ := by
      rw [← pow_add, ← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      nlinarith

end

end

end SpectralBooks
end LinearAlgebra
end OAI

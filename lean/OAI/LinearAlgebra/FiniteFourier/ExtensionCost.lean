import OAI.LinearAlgebra.FiniteFourier.ExtensionProduct
import OAI.LinearAlgebra.FiniteFourier.CircuitComposition
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex

/-! # Circuit cost of multiplication in a power basis

The ordinary product is computed once. Its low part is retained while its
reversed high part feeds the reciprocal-modulus and quotient products.
Subtracting the correction costs one binary gate in each output coordinate.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial ExactFourier.CoefficientTime
open scoped PowerSeries

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

private theorem subtraction_circuit {I : Type*} (t : Finset I) :
    ∃ n ≤ t.card, ∃ p : Circuit K (I ⊕ I) I n, ∀ i ∈ t, ∀ x,
      p.eval x i = x (.inl i) - x (.inr i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp, ⟨.nil, fun _ => .zero⟩, by simp⟩
  | @insert j t hj ih =>
    obtain ⟨n, hn, p, hp⟩ := ih
    let gate : BinaryGate K ((I ⊕ I) ⊕ Fin 0) := ⟨.inl (.inl j), .inl (.inr j), 1, -1⟩
    let q : Circuit K (I ⊕ I) Unit 1 := ⟨Program.nil.step gate, fun _ => .scaled 1 (.inr 0)⟩
    obtain ⟨m, hm, r, hr⟩ := circuit_fanout q p
    refine ⟨m, by rw [Finset.card_insert_of_notMem hj]; omega, ⟨r.program, fun i =>
      r.output (if i = j then .inl () else .inr i)⟩, fun i hi x => ?_⟩
    change r.eval x (if i = j then .inl () else .inr i) = _
    rw [hr]
    by_cases h : i = j
    · subst i
      simp [q, gate, Circuit.eval, Readout.eval, Program.value, BinaryGate.eval, sub_eq_add_neg]
    · simpa [h] using hp i ((Finset.mem_insert.mp hi).resolve_left h) x

/-- Realize the three fixed Toeplitz calls in the power-basis reduction, retaining
the ordinary product for its second use. -/
theorem fixedScalarCoordinates_circuit (cost : ℕ → ℕ)
    (hcost : ∀ n (f : K⟦X⟧), RealizableAtMost (truncMatrix n f) (cost n))
    (e : ℕ) (m s : K[X]) :
    ∃ n ≤ cost (2 * e) + 2 * cost e + e, ∃ r : Circuit K (Fin e) (Fin e) n,
      ∀ x, r.eval x = fixedScalarCoordinates e m s x := by
  classical
  obtain ⟨s₁, h₁, p₁, hp₁⟩ := hcost (2 * e) (s : K⟦X⟧)
  obtain ⟨s₂, h₂, p₂, hp₂⟩ := hcost e ((m.reflect e : K⟦X⟧)⁻¹)
  obtain ⟨s₃, h₃, p₃, hp₃⟩ := hcost e (m : K⟦X⟧)
  let pad : Circuit K (Fin e) (Fin (2 * e)) 0 :=
    ⟨.nil, fun j => if h : j.val < e then .scaled 1 (.inl ⟨j.val, h⟩) else .zero⟩
  have hpad (x : Fin e → K) (j : Fin (2 * e)) :
      pad.eval x j = (if h : j.val < e then x ⟨j.val, h⟩ else 0) := by
    by_cases h : j.val < e <;> simp [pad, Circuit.eval, h, Readout.eval]
  obtain ⟨ny, hny, y, hy⟩ := circuit_comp pad p₁
  let high (j : Fin e) : Fin (2 * e) := ⟨e + (e - 1) - j.val, by have := j.isLt; omega⟩
  let low (j : Fin e) : Fin (2 * e) := ⟨j.val, by have := j.isLt; omega⟩
  let p₂' := p₂.rewire (fun j => ((1 : K), high j)) (fun j : Fin e => ((1 : K), j.rev))
  obtain ⟨nc, hnc, corr, hcorr⟩ := circuit_comp p₂' p₃
  let takeLow : Circuit K (Fin (2 * e)) (Fin e) 0 := ⟨.nil, fun i => .scaled 1 (.inl (low i))⟩
  obtain ⟨nr, hnr, both, hboth⟩ := circuit_fanout takeLow corr
  obtain ⟨nu, hnu, entire, hentire⟩ := circuit_comp y both
  obtain ⟨nv, hnv, sub, hsub⟩ := subtraction_circuit (K := K) (Finset.univ : Finset (Fin e))
  obtain ⟨nw, hnw, result, hresult⟩ := circuit_comp entire sub
  refine ⟨nw, by simp at hnv; omega, result, fun x => ?_⟩
  funext i
  rw [hresult, hsub i (Finset.mem_univ i), hentire, hboth]
  simp only [Sum.elim_inl, Sum.elim_inr, hcorr]
  have hlow (z : Fin (2 * e) → K) : takeLow.eval z i = z (low i) := by
    simp [takeLow, Circuit.eval, Readout.eval]
  have hrev (z : Fin (2 * e) → K) (j : Fin e) :
      p₂'.eval z j = (truncMatrix e ((m.reflect e : K⟦X⟧)⁻¹)).mulVec (fun k => z (high k)) j.rev := by
    simp [p₂', Circuit.eval_rewire, p₂.eval_eq_mulVec, hp₂]
  rw [hlow, p₃.eval_eq_mulVec, hp₃]
  simp_rw [show p₂'.eval (y.eval x) = fun j => _ from funext (hrev (y.eval x)), hy,
    p₁.eval_eq_mulVec, hp₁, show pad.eval x = _ from funext (hpad x)]
  rfl

/-- The matrix of multiplication by a fixed extension scalar in a power basis
of dimension `e` costs at most `cost (2e) + 2 cost e + e` binary gates. -/
theorem realizable_powerBasis_scalar (cost : ℕ → ℕ)
    (hcost : ∀ n (f : K⟦X⟧), RealizableAtMost (truncMatrix n f) (cost n))
    (pb : PowerBasis K E) (u : E) :
    RealizableAtMost (fun i j => pb.basis.repr (u * pb.basis j) i)
      (cost (2 * pb.dim) + 2 * cost pb.dim + pb.dim) := by
  classical
  obtain ⟨s, _, hs⟩ := powerBasis_scalar_coordinates pb u
  obtain ⟨n, hn, r, hr⟩ := fixedScalarCoordinates_circuit cost hcost pb.dim (minpoly K pb.gen) s
  refine ⟨n, hn, r, ?_⟩
  ext i j
  unfold Circuit.matrix
  rw [hr, hs]
  simp [Pi.single_apply, ite_smul]

end

end FiniteFourier
end LinearAlgebra
end OAI

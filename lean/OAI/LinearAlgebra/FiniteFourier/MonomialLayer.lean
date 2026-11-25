import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization
import OAI.LinearAlgebra.FiniteFourier.ScalarDescent
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel

/-!
# Monomial layers under restriction of scalars

Each monomial layer has one unit in each row and column. After a permutation
of the input coordinates, scalar restriction decomposes it into one
multiplication over the ground field for every row.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
open scoped BigOperators Kronecker

variable {E : Type*} [CommRing E] {I : Type} [Fintype I] [DecidableEq I]

/-- The permutation and nonzero row factors of a synchronized monomial layer. -/
theorem LayerMatrix.monomial_form {A : Matrix I I E} (hA : LayerMatrix .monomial A) :
    ∃ (p : Equiv.Perm I) (c : I → Eˣ), ∀ i j,
      A i j = if p i = j then (c i : E) else 0 := by
  generalize hk : LayerKind.monomial = k at hA
  induction hA with
  | id k =>
    refine ⟨Equiv.refl _, fun _ => 1, fun i j => ?_⟩
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  | monomial e d => exact ⟨e, d, fun _ _ => rfl⟩
  | unitShear => contradiction
  | relabel e _ ih =>
    obtain ⟨p, c, h⟩ := ih hk
    refine ⟨(e.symm.trans p).trans e, fun i => c (e.symm i), fun i j => ?_⟩
    simp [Matrix.submatrix, h, ← e.eq_symm_apply]
  | tensor _ _ ihA ihB =>
    obtain ⟨p, c, ha⟩ := ihA hk
    obtain ⟨q, d, hb⟩ := ihB hk
    refine ⟨p.prodCongr q, fun i => c i.1 * d i.2, ?_⟩
    rintro ⟨i, k⟩ ⟨j, l⟩
    by_cases h : p i = j <;> by_cases g : q k = l <;>
      simp [Matrix.kroneckerMap_apply, ha, hb, h, g]
  | parallel _ _ ihA ihB =>
    obtain ⟨p, c, ha⟩ := ihA hk
    obtain ⟨q, d, hb⟩ := ihB hk
    refine ⟨p.sumCongr q, Sum.elim c d, ?_⟩
    rintro (i | i) (j | j) <;> simp [Matrix.fromBlocks, ha, hb]
  | grid _ ih =>
    choose p c h using fun i => ih i hk
    refine ⟨Equiv.piCongrRight p, fun x => ∏ i, c i (x i), fun x y => ?_⟩
    by_cases he : (Equiv.piCongrRight p) x = y
    · subst y
      simp [gridTensor, h]
    · obtain ⟨i, hi⟩ : ∃ i, p i (x i) ≠ y i := by
        contrapose! he
        exact funext he
      rw [ite_eq_right he]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h, hi])
  | blocks _ ih =>
    choose p c h using fun i => ih i hk
    refine ⟨Equiv.sigmaCongrRight p, fun x => c x.1 x.2, ?_⟩
    rintro ⟨k, i⟩ ⟨l, j⟩
    by_cases he : k = l
    · subst l
      simp [h, Equiv.sigmaCongrRight]
    · simp [Matrix.blockDiagonal'_apply', Equiv.sigmaCongrRight, Sigma.ext_iff, he]

section Restriction

variable {K D : Type*} [CommRing K] [Algebra K E] [Fintype D]

omit [Fintype I] [Fintype D] in
/-- After permuting its inputs, restriction of a monomial matrix consists of
independent blocks of multiplication by the row units. -/
theorem restrictMatrix_monomial {A : Matrix I I E} (b : Module.Basis D K E)
    (p : Equiv.Perm I) (c : I → Eˣ)
    (h : ∀ i j, A i j = if p i = j then (c i : E) else 0) :
    restrictMatrix b A =
      Matrix.reindex (Equiv.prodComm D I)
        ((Equiv.prodComm D I).trans (p.prodCongr (Equiv.refl D)))
        (Matrix.blockDiagonal fun i : I => (fun d u : D => b.repr ((c i : E) * b u) d)) := by
  ext ⟨i, d⟩ ⟨j, u⟩
  change b.repr (A i j * b u) d = if i = p.symm j then b.repr ((c i : E) * b u) d else 0
  by_cases hij : p i = j <;> simp [h, p.eq_symm_apply, hij]

/-- A monomial layer descends at the sum of the individual row multiplication
costs. Both the row indexing permutation and the units are returned. -/
theorem LayerMatrix.restrictMatrix_monomial_cost {A : Matrix I I E}
    (hA : LayerMatrix .monomial A) (b : Module.Basis D K E) (cost : Eˣ → ℕ)
    (hc : ∀ a : Eˣ, RealizableAtMost (fun d u : D => b.repr ((a : E) * b u) d) (cost a)) :
    ∃ (p : Equiv.Perm I) (c : I → Eˣ),
      (∀ i j, A i j = if p i = j then (c i : E) else 0) ∧
        RealizableAtMost (restrictMatrix b A) (∑ i, cost (c i)) := by
  obtain ⟨p, c, h⟩ := hA.monomial_form
  refine ⟨p, c, h, ?_⟩
  rw [restrictMatrix_monomial b p c h]
  exact (RealizableAtMost.blockDiagonal_family (fun i => hc (c i))).reindex _ _

/-- A uniform scalar multiplication cost bounds a descended monomial layer. -/
theorem LayerMatrix.restrictMatrix_monomial_uniform {A : Matrix I I E}
    (hA : LayerMatrix .monomial A) (b : Module.Basis D K E) {s : ℕ}
    (hc : ∀ a : Eˣ, RealizableAtMost (fun d u : D => b.repr ((a : E) * b u) d) s) :
    RealizableAtMost (restrictMatrix b A) (Fintype.card I * s) := by
  obtain ⟨_, _, _, h⟩ := hA.restrictMatrix_monomial_cost b (fun _ => s) hc
  simpa using h

end Restriction

end FiniteFourier
end LinearAlgebra
end OAI

import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPrune
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Specializing table entries in a single ordered pruning

The tree and all its edge dimensions are shared across evaluations of the input tables.
Specializing a table by a homomorphism commutes with contraction at every boundary assignment.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V K R : Type*} {d : V → ℕ}

namespace OrderedTensorTree

/-- Apply a scalar map to each table entry, preserving the ordered tree. -/
def map (f : K → R) : {q : ℕ} → OrderedTensorTree K d q → OrderedTensorTree R d q
  | _, .scalar v => .scalar (fun o => f (v o))
  | _, .stub j M => .stub j (fun o a => f (M o a))
  | _, .unary M t => .unary (fun o a => f (M o a)) (t.map f)
  | _, .branch B t u => .branch (fun o a b => f (B o a b)) (t.map f) (u.map f)

theorem eval_map [CommSemiring K] [CommSemiring R] (f : K →+* R) {q : ℕ}
    (t : OrderedTensorTree K d q) (x : ∀ j, Fin (d j)) (o : Fin q) :
    (t.map f).eval x o = f (t.eval x o) := by
  induction t with
  | scalar => rfl
  | stub => simp [map, eval, linEval, boundaryValue, apply_ite]
  | unary _ _ ih => simp [map, eval, linEval, ih]
  | branch _ _ _ ih jh => simp [map, eval, triEval, ih, jh]

end OrderedTensorTree

namespace TrivalentTree

/-- Apply a scalar map to every trivalent table. The ports retain their labels and dimensions. -/
def map (f : K → R) : {q : ℕ} → TrivalentTree K d q → TrivalentTree R d q
  | _, .port j => .port j
  | _, .branch B t u => .branch (fun o a b => f (B o a b)) (t.map f) (u.map f)

@[simp] theorem labels_map (f : K → R) {q : ℕ} (t : TrivalentTree K d q) :
    (t.map f).labels = t.labels := by induction t <;> simp [map, labels, *]

@[simp] theorem vertices_map (f : K → R) {q : ℕ} (t : TrivalentTree K d q) :
    (t.map f).vertices = t.vertices := by induction t <;> simp [map, vertices, *]

@[simp] theorem bounded_map (f : K → R) {q m : ℕ} (t : TrivalentTree K d q) :
    (t.map f).Bounded m ↔ t.Bounded m := by induction t <;> simp [map, Bounded, *]

theorem eval_map [CommSemiring K] [CommSemiring R] (f : K →+* R) {q : ℕ}
    (t : TrivalentTree K d q) (x : ∀ j, Fin (d j)) (o : Fin q) :
    (t.map f).eval x o = f (t.eval x o) := by
  induction t with
  | port v => by_cases h : o = x v <;> simp [map, eval, boundaryValue, h]
  | branch _ _ _ ih jh => simp [map, eval, triEval, ih, jh]

end TrivalentTree

/-- A pruning obtained with symbolic entries specializes simultaneously over all
homomorphisms into a commutative semiring. -/
theorem OrderedTensorTree.trivalent_pruning_specializes [CommSemiring K] [CommSemiring R]
    {q m : ℕ} (t : OrderedTensorTree K d q) (h : t.Bounded m) (hports : 2 ≤ t.labels.length) :
    ∃ u : TrivalentTree K d q, u.labels = t.labels ∧ u.Bounded m ∧
      u.vertices + 2 = t.labels.length + 1 ∧ ∀ (f : K →+* R) x,
        (u.map f).eval x = (t.map f).eval x := by
  obtain ⟨u, hl, hb, hv, he⟩ := t.trivalent_pruning h hports
  refine ⟨u, hl, hb, hv, fun f x => ?_⟩
  funext o
  rw [TrivalentTree.eval_map, OrderedTensorTree.eval_map, he]

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI

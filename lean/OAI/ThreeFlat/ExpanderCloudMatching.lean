import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

namespace OAI
/-! # Matching ports between clouds

The ports at each vertex of a symmetric integer arc table are labeled by
destination and arc number. Reversing the endpoints and keeping the arc
number gives the required matching, including fixed points for loops.
-/

namespace ThreeFlat

open scoped BigOperators

/-- A symmetric arc table with row sums `q` is realized by an involution of
the `q` ports at each vertex. -/
theorem exists_cloudMatching {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (c : V → V → ℕ) (hsym : ∀ u v, c u v = c v u)
    (hrow : ∀ u, ∑ v, c u v = q) :
    ∃ e : Equiv.Perm (V × Fin q), Function.Involutive e ∧
      ∀ u v, (Finset.univ.filter (fun p : Fin q => (e (u, p)).1 = v)).card = c u v := by
  classical
  let label (u : V) : Fin q ≃ Σ v, Fin (c u v) :=
    Fintype.equivOfCardEq (by simp [hrow u])
  let ports := Σ u, Σ v, Fin (c u v)
  let pack : ports ≃ V × Fin q := Equiv.sigmaEquivProdOfEquiv fun u => (label u).symm
  let rev (a : ports) : ports :=
    ⟨a.2.1, a.1, a.2.2.cast (hsym a.1 a.2.1)⟩
  have hrev : Function.Involutive rev := by rintro ⟨u, v, i⟩; rfl
  let flip : Equiv.Perm ports := ⟨rev, rev, hrev, hrev⟩
  let e := (pack.symm.trans flip).trans pack
  refine ⟨e, ?_, ?_⟩
  · intro a
    change pack (rev (pack.symm (pack (rev (pack.symm a))))) = a
    rw [pack.symm_apply_apply, hrev, pack.apply_symm_apply]
  intro u v
  change (Finset.univ.filter (fun p : Fin q => (label u p).1 = v)).card = c u v
  calc
    _ = ∑ p : Fin q, if (label u p).1 = v then 1 else 0 := by
      simp [← Finset.sum_filter]
    _ = ∑ z : Σ w, Fin (c u w), if z.1 = v then 1 else 0 :=
      (label u).sum_comp (fun z => if z.1 = v then (1 : ℕ) else 0)
    _ = c u v := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single v]
      · simp
      · intro w _ hw
        simp [hw]
      · simp

/-- Summing a value over ports in a cloud weights each destination by its
arc multiplicity. -/
theorem cloudMatching_sum {V M : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid M]
    {q : ℕ} {e : Equiv.Perm (V × Fin q)} {c : V → V → ℕ}
    (hcount : ∀ u v, (Finset.univ.filter (fun p : Fin q => (e (u, p)).1 = v)).card = c u v)
    (u : V) (f : V → M) :
    (∑ p : Fin q, f (e (u, p)).1) = ∑ v, c u v • f v := by
  calc
    _ = ∑ p : Fin q, ∑ v, if (e (u, p)).1 = v then f v else 0 := by simp
    _ = ∑ v, ∑ p : Fin q, if (e (u, p)).1 = v then f v else 0 := Finset.sum_comm
    _ = _ := by simp_rw [← Finset.sum_filter, Finset.sum_const, hcount]

end ThreeFlat

end OAI

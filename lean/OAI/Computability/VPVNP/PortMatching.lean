import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-!
# Matching ports with prescribed transition counts

In the replacement construction of Section 5.3 of *VP and VNP differ over
every field*, vertex `v` gets `Q` ports. Its ports are indexed by a
destination `w` and an arc number in `Fin (a v w)`. Reversing an arc
keeps this number, so symmetry of the multiplicity matrix gives an
involution, with the ports for self-transitions fixed individually.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {V : Type*} [Fintype V] [DecidableEq V] {Q : ℕ}

/-- A symmetric matrix of natural arc multiplicities with row sums `Q` is
realized by an involution on `Q` ports at each vertex. -/
theorem exists_portMatching (a : V → V → ℕ)
    (hsym : ∀ v w, a v w = a w v) (hrow : ∀ v, ∑ w, a v w = Q) :
    ∃ σ : Equiv.Perm (V × Fin Q), Function.Involutive σ ∧
      (∀ v w, (Finset.univ.filter (fun k : Fin Q ↦ (σ (v, k)).1 = w)).card = a v w) ∧
      (∀ p, (σ p).1 = p.1 → σ p = p) := by
  let label (v : V) : (Σ w, Fin (a v w)) ≃ Fin Q :=
    Fintype.equivFinOfCardEq (by simpa using hrow v)
  let reverse (p : V × Fin Q) : V × Fin Q :=
    let e := (label p.1).symm p.2
    (e.1, label e.1 ⟨p.1, Fin.cast (hsym p.1 e.1) e.2⟩)
  have edge (v w : V) (i : Fin (a v w)) :
      reverse (v, label v ⟨w, i⟩) = (w, label w ⟨v, Fin.cast (hsym v w) i⟩) := by
    exact congrArg (fun e : Σ u, Fin (a v u) ↦
      (e.1, label e.1 ⟨v, Fin.cast (hsym v e.1) e.2⟩)) ((label v).symm_apply_apply _)
  have hinv : Function.Involutive reverse := by
    rintro ⟨v, k⟩
    obtain ⟨⟨w, i⟩, rfl⟩ := (label v).surjective k
    simp [edge]
  let σ : Equiv.Perm (V × Fin Q) := ⟨reverse, reverse, hinv, hinv⟩
  refine ⟨σ, hinv, ?_, ?_⟩
  · intro v w
    rw [Finset.card_filter]
    calc
      _ = ∑ e : Σ u, Fin (a v u), if e.1 = w then 1 else 0 :=
        Fintype.sum_equiv (label v).symm _ _ (fun _ ↦ rfl)
      _ = ∑ u, if u = w then a v u else 0 := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro u _
        by_cases h : u = w <;> simp [h]
      _ = a v w := by simp
  · rintro ⟨v, k⟩
    obtain ⟨⟨w, i⟩, rfl⟩ := (label v).surjective k
    change (reverse _).1 = v → reverse _ = _
    rw [edge]
    intro h
    change w = v at h
    subst w
    rfl

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The replacement puts the graph on `K` inside each cloud and adds `h`
copies of each port's matching arc. -/
def replacementArcs (H : K → K → ℕ) (σ : Equiv.Perm (V × K)) (h : ℕ)
    (p q : V × K) : ℕ :=
  (if q.1 = p.1 then H p.2 q.2 else 0) + (if q = σ p then h else 0)

omit [Fintype V] [Fintype K] in
theorem replacementArcs_symmetric (H : K → K → ℕ) (hs : ∀ i j, H i j = H j i)
    (σ : Equiv.Perm (V × K)) (hi : Function.Involutive σ) (h : ℕ) (p q : V × K) :
    replacementArcs H σ h p q = replacementArcs H σ h q p := by
  have hmatch : q = σ p ↔ p = σ q := ⟨fun e ↦ by rw [e, hi], fun e ↦ by rw [e, hi]⟩
  simp only [replacementArcs, hmatch, hs p.2 q.2, eq_comm (a := q.1) (b := p.1)]

/-- Each vertex in the replacement has the original degree `2 * h`. -/
theorem replacementArcs_degree (H : K → K → ℕ) (h : ℕ) (hrow : ∀ i, ∑ j, H i j = h)
    (σ : Equiv.Perm (V × K)) (p : V × K) : ∑ q, replacementArcs H σ h p q = 2 * h := by
  simp only [replacementArcs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Nat.two_mul]
  congr 1
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ v, if v = p.1 then h else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v = p.1 <;> simp [hv, hrow]
    _ = h := by simp

/-- The final graph in Section 5.3 takes each old edge across the two layers
and adds `b` vertical arcs at each vertex. -/
def layerArcs (G : V → V → ℕ) (b : ℕ) (p q : V × Bool) : ℕ :=
  if q.2 = !p.2 then G p.1 q.1 + (if q.1 = p.1 then b else 0) else 0

omit [Fintype V] in
theorem layerArcs_symmetric (G : V → V → ℕ) (hs : ∀ i j, G i j = G j i)
    (b : ℕ) (p q : V × Bool) : layerArcs G b p q = layerArcs G b q p := by
  obtain ⟨u, i⟩ := p
  obtain ⟨v, j⟩ := q
  cases i <;> cases j <;> simp [layerArcs, hs u v, eq_comm (a := v) (b := u)]

omit [Fintype V] in
theorem layerArcs_no_loops (G : V → V → ℕ) (b : ℕ) (p : V × Bool) : layerArcs G b p p = 0 := by
  cases p with
  | mk v i => cases i <;> rfl

theorem layerArcs_degree (G : V → V → ℕ) (b : ℕ) (hrow : ∀ u, ∑ v, G u v = b)
    (p : V × Bool) : ∑ q, layerArcs G b p q = 2 * b := by
  rw [Fintype.sum_prod_type]
  simp [layerArcs, Finset.sum_add_distrib, hrow, Nat.two_mul]

end SpectralGeometry

end VPVNP
end Computability
end OAI

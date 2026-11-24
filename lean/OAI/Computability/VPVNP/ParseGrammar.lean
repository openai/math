import OAI.Computability.VPVNP.OrderedParse
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Graded parse tables for arithmetic circuits

Section 8.1 of *VP and VNP differ over every field* uses an ordered binary grammar to
record a homogeneous component of a circuit output. Here the layer index `d : Fin n`
represents degree `d.val + 1`. Each production has its own scalar, including a separate
scalar for each choice of terminal variable.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

/-- Scalar labels on all terminals and ordered binary productions through degree `n`. -/
structure ParseGrammar (R V H : Type*) (n : ℕ) where
  /-- The scalar weight for emitting terminal variable `v` from state `h` in degree one. -/
  terminal : H → V → R
  /-- The scalar weight for a binary production at layer `d`, given its parent state, split and
  ordered child states. -/
  binary : (d : Fin n) → H → Fin d.val → H → H → R

namespace ParseGrammar

variable {R V H : Type*} {n : ℕ}

/-- Layer of the left child at split `b`. Its degree is `b.val + 1`. -/
def leftDegree (d : Fin n) (b : Fin d.val) : Fin n :=
  ⟨b.val, b.isLt.trans d.isLt⟩

/-- Layer of the right child. Its degree is the remaining `d.val - b.val`. -/
def rightDegree (d : Fin n) (b : Fin d.val) : Fin n :=
  ⟨d.val - 1 - b.val, by have := b.isLt; have := d.isLt; omega⟩

theorem leftDegree_lt (d : Fin n) (b : Fin d.val) : (leftDegree d b).val < d.val :=
  b.isLt

theorem rightDegree_lt (d : Fin n) (b : Fin d.val) : (rightDegree d b).val < d.val := by
  change d.val - 1 - b.val < d.val
  have := b.isLt
  omega

theorem split_degrees (d : Fin n) (b : Fin d.val) :
    ((leftDegree d b).val + 1) + ((rightDegree d b).val + 1) = d.val + 1 := by
  change b.val + 1 + (d.val - 1 - b.val + 1) = d.val + 1
  have := b.isLt
  omega

variable [Fintype V] [Fintype H] [CommSemiring R]

/-- Evaluate a grammar state as a formal polynomial by multiplying the two ordered
children of each binary production and summing over all productions. -/
noncomputable def eval (G : ParseGrammar R V H n) (d : Fin n) (h : H) : MvPolynomial V R :=
  if d.val = 0 then ∑ v, C (G.terminal h v) * X v
  else ∑ b, ∑ i, ∑ j,
    C (G.binary d h b i j) * G.eval (leftDegree d b) i * G.eval (rightDegree d b) j
termination_by d.val
decreasing_by
  all_goals first | exact leftDegree_lt _ _ | exact rightDegree_lt _ _

theorem eval_terminal (G : ParseGrammar R V H n) {d : Fin n} (hd : d.val = 0) (h : H) :
    G.eval d h = ∑ v, C (G.terminal h v) * X v := by
  rw [eval]; simp [hd]

theorem eval_binary (G : ParseGrammar R V H n) {d : Fin n} (hd : d.val ≠ 0) (h : H) :
    G.eval d h = ∑ b, ∑ i, ∑ j,
      C (G.binary d h b i j) * G.eval (leftDegree d b) i * G.eval (rightDegree d b) j := by
  rw [eval]; simp [hd]

/-- The recursive evaluation agrees with every state table that satisfies the grammar
equations, simultaneously for all states and positive degrees through `n`. -/
theorem eval_eq_of_recurrence (G : ParseGrammar R V H n) (f : Fin n → H → MvPolynomial V R)
    (hterminal : ∀ d h, d.val = 0 → f d h = ∑ v, C (G.terminal h v) * X v)
    (hbinary : ∀ d h, d.val ≠ 0 → f d h = ∑ b, ∑ i, ∑ j,
      C (G.binary d h b i j) * f (leftDegree d b) i * f (rightDegree d b) j)
    (d : Fin n) (h : H) : G.eval d h = f d h := by
  induction d using (measure (fun d : Fin n ↦ d.val)).wf.induction generalizing h with
  | h d ih =>
    by_cases hd : d.val = 0
    · rw [eval_terminal _ hd, hterminal _ _ hd]
    · rw [eval_binary _ hd, hbinary _ _ hd]
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      rw [ih _ (leftDegree_lt d b) i, ih _ (rightDegree_lt d b) j]

/-- Every state polynomial is homogeneous in the input variables of its declared degree. -/
theorem eval_isHomogeneous (G : ParseGrammar R V H n) (d : Fin n) (h : H) :
    (G.eval d h).IsHomogeneous (d.val + 1) := by
  induction d using (measure (fun d : Fin n ↦ d.val)).wf.induction generalizing h with
  | h d ih =>
    by_cases hd : d.val = 0
    · rw [eval_terminal _ hd, hd]
      refine IsHomogeneous.sum _ _ _ fun v _ ↦ ?_
      simpa using (isHomogeneous_C V (G.terminal h v)).mul (isHomogeneous_X R v)
    · rw [eval_binary _ hd]
      refine IsHomogeneous.sum _ _ _ fun b _ ↦ IsHomogeneous.sum _ _ _ fun i _ ↦
        IsHomogeneous.sum _ _ _ fun j _ ↦ ?_
      simpa [split_degrees] using
        ((isHomogeneous_C V (G.binary d h b i j)).mul (ih _ (leftDegree_lt d b) i)).mul
          (ih _ (rightDegree_lt d b) j)


variable (G : ParseGrammar R V H n)

/-- Multiply the terminal and internal scalar labels occurring in this ordered parse. -/
def weight (G : ParseGrammar R V H n) (d : Fin n) (h : H) (p : OrderedParse V H d.val) : R :=
  match d, p with
  | ⟨0, _⟩, .leaf v => G.terminal h v
  | ⟨k + 1, hk⟩, .node b i j l r =>
    G.binary ⟨k + 1, hk⟩ h b i j *
      G.weight (leftDegree ⟨k + 1, hk⟩ b) i l *
      G.weight (rightDegree ⟨k + 1, hk⟩ b) j r
termination_by d.val
decreasing_by
  all_goals first | exact leftDegree_lt _ _ | exact rightDegree_lt _ _

omit [Fintype V] [Fintype H] in
@[simp] theorem weight_leaf (hn : 0 < n) (h : H) (v : V) :
    G.weight ⟨0, hn⟩ h (.leaf v) = G.terminal h v := by
  rw [weight]

omit [Fintype V] [Fintype H] in
@[simp] theorem weight_node {k : ℕ} (hk : k + 1 < n) (h : H) (b : Fin (k + 1))
    (i j : H) (l : OrderedParse V H b.val) (r : OrderedParse V H (k - b.val)) :
    G.weight ⟨k + 1, hk⟩ h (.node b i j l r) =
      G.binary ⟨k + 1, hk⟩ h b i j *
      G.weight (leftDegree ⟨k + 1, hk⟩ b) i l *
      G.weight (rightDegree ⟨k + 1, hk⟩ b) j r := by
  rw [weight]

/-- Expansion of the state polynomial as a sum over the actual ordered parse trees.
The multiplicative terminal monomial reads the leaves in their left-to-right order. -/
theorem eval_eq_sum (d : Fin n) (h : H) :
    G.eval d h = ∑ p : OrderedParse V H d.val,
      C (G.weight d h p) * (p.leaves.map (X (R := R))).prod := by
  classical
  apply G.eval_eq_of_recurrence
    (fun d h ↦ ∑ p : OrderedParse V H d.val, C (G.weight d h p) * (p.leaves.map X).prod)
  · rintro ⟨d, hd⟩ h rfl
    rw [← (OrderedParse.leafEquiv (V := V) (H := H)).symm.sum_comp]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    change C (G.weight ⟨0, hd⟩ h (.leaf v)) * (List.map X [v]).prod = _
    simp
  · rintro ⟨k, hk⟩ h hpos
    cases k with
    | zero => exact (hpos rfl).elim
    | succ k =>
      rw [← (OrderedParse.nodeEquiv (V := V) (H := H) k).symm.sum_comp]
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      change C (G.weight ⟨k+1, hk⟩ h (.node b i j l r)) *
        (List.map X (l.leaves ++ r.leaves)).prod = _
      simp only [weight_node, map_mul, List.map_append, List.prod_append]
      ac_rfl

/-- Evaluate the parse expansion with arbitrary terminal values and a change of scalars. -/
theorem eval₂_eq_sum {S : Type*} [CommSemiring S] (scalar : R →+* S) (input : V → S)
    (d : Fin n) (h : H) :
    eval₂Hom scalar input (G.eval d h) = ∑ p : OrderedParse V H d.val,
      scalar (G.weight d h p) * (p.leaves.map input).prod := by
  rw [G.eval_eq_sum]
  simp only [map_sum, map_mul, eval₂Hom_C, map_list_prod, List.map_map]
  simp [Function.comp_def]

end ParseGrammar

end VPVNP
end Computability
end OAI

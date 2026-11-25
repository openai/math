import OAI.Computability.BorderVNP.Model

/-!
# Simultaneous border approximations in a crossing

In §4.4 each first side has its own set of attainable splits. Fixing all other
tables specializes a polynomial equation to a polynomial in one side. Successively
using the closures for these independent inputs therefore gives a point in the
closure of the joint attainable sums.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open MvPolynomial
open scoped BigOperators

variable {I K : Type*} {κ : I → Type*} [Field K]

/-- A product of independently attainable table sets, with all entries regarded as one
affine coordinate vector. -/
def jointTables (S : ∀ i, Set (κ i → K)) : Set ((i : I) × κ i → K) :=
  {a | ∀ i, (fun j => a ⟨i, j⟩) ∈ S i}

/-- Specializing all but one table preserves polynomiality in the remaining entries. -/
private theorem polynomial_slice [DecidableEq I] (q : MvPolynomial ((i : I) × κ i) K)
    (y : ∀ i, κ i → K) (i : I) :
    ∃ r : MvPolynomial (κ i) K, ∀ z : κ i → K,
      eval z r = eval (Sigma.uncurry (Function.update y i z)) q := by
  let block : ∀ j, κ j → MvPolynomial (κ i) K :=
    Function.update (fun j k => C (y j k)) i X
  refine ⟨eval₂ C (Sigma.uncurry block) q, fun z => ?_⟩
  rw [← eval_assoc]
  apply congrArg (fun v => eval v q)
  funext ⟨j, k⟩
  by_cases hj : j = i
  · subst j
    simp [block, Sigma.uncurry]
  · simp [block, Sigma.uncurry, hj]

variable [Fintype I]

/-- For a finite collection of independent inputs, closing each set of tables separately
gives exactly the Zariski closure of the jointly attainable table vectors. -/
theorem imageClosure_jointTables (S : ∀ i, Set (κ i → K)) :
    imageClosure (jointTables S) = jointTables (fun i => imageClosure (S i)) := by
  classical
  ext a
  constructor
  · intro ha i
    have h := imageClosure_polynomial ha (fun k : κ i => X (R := K) ⟨i, k⟩)
    simp only [eval_X] at h
    apply imageClosure_mono _ h
    rintro _ ⟨y, hy, rfl⟩
    exact hy i
  · intro ha q hq
    have aux (s : Finset I) (y : ∀ i, κ i → K) (hc : ∀ i ∈ s, y i ∈ imageClosure (S i))
        (he : ∀ i ∉ s, y i ∈ S i) : eval (Sigma.uncurry y) q = 0 := by
      induction s using Finset.induction_on generalizing y with
      | empty => exact hq _ (fun i => he i (Finset.notMem_empty i))
      | @insert i s hi ih =>
        obtain ⟨r, hr⟩ := polynomial_slice q y i
        have hzero := hc i (Finset.mem_insert_self ..) r (fun z hz => by
          rw [hr]
          apply ih
          · intro j hj
            have hji : j ≠ i := fun e => hi (e ▸ hj)
            simpa only [Function.update_of_ne hji] using hc j (Finset.mem_insert_of_mem hj)
          · intro j hj
            by_cases hji : j = i
            · subst j
              simpa only [Function.update_self] using hz
            · simpa only [Function.update_of_ne hji] using he j (by simp [hji, hj]))
        simpa only [hr, Function.update_eq_self] using hzero
    exact aux Finset.univ (fun i j => a ⟨i, j⟩) (fun i _ => ha i) (by simp)

/-- A polynomial contraction of independently approximated sides lies in the closure of
the contractions obtained by choosing actual parameters on every side. -/
theorem imageClosure_joint_contraction {O : Type*} {P : I → Type*}
    (side : ∀ i, P i → κ i → K) (a : ∀ i, κ i → K)
    (ha : ∀ i, a i ∈ imageClosure (Set.range (side i)))
    (Q : O → MvPolynomial ((i : I) × κ i) K) :
    (fun o => eval (Sigma.uncurry a) (Q o)) ∈ imageClosure
      (Set.range fun p : ∀ i, P i => fun o => eval (Sigma.uncurry fun i => side i (p i)) (Q o)) := by
  have h : Sigma.uncurry a ∈ imageClosure (jointTables (fun i => Set.range (side i))) := by
    rw [imageClosure_jointTables]
    exact ha
  apply imageClosure_mono _ (imageClosure_polynomial h Q)
  rintro _ ⟨y, hy, rfl⟩
  choose p hp using hy
  refine ⟨p, ?_⟩
  have he : (Sigma.uncurry fun i => side i (p i)) = y := by
    funext ⟨i, j⟩
    exact congrFun (hp i) j
  exact congrArg (fun z o => eval z (Q o)) he

/-- Contract each approximated first-side table against a fixed opposite-side table and sum
over orientations. This is the linear contraction used in the last paragraph of §4.4. -/
theorem imageClosure_sum_contractions {O : Type*} {P : I → Type*} [∀ i, Fintype (κ i)]
    (side : ∀ i, P i → κ i → K) (a : ∀ i, κ i → K)
    (ha : ∀ i, a i ∈ imageClosure (Set.range (side i)))
    (weights : ∀ i, O → κ i → K) :
    (fun o => ∑ i, ∑ j, weights i o j * a i j) ∈ imageClosure
      (Set.range fun p : ∀ i, P i => fun o => ∑ i, ∑ j, weights i o j * side i (p i) j) := by
  let Q (o : O) : MvPolynomial ((i : I) × κ i) K :=
    ∑ i, ∑ j, C (weights i o j) * X ⟨i, j⟩
  have eqv (v : ∀ i, κ i → K) (o : O) :
      eval (Sigma.uncurry v) (Q o) = ∑ i, ∑ j, weights i o j * v i j := by
    simp only [Q, map_sum, map_mul, eval_C, eval_X, Sigma.uncurry]
  simpa only [eqv] using imageClosure_joint_contraction side a ha Q

end Crossing

end BorderVNP
end Computability
end OAI

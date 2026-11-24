import OAI.Computability.VPVNP.CompressionSchedule
import OAI.Computability.VPVNP.CompressionProcedure

/-!
# Executing one block of scheduled compression

The shrinking steps are composed in their chosen order. Each step retains
its execution tree for every branch of the preceding exact kernel. The final
refresh restores the initial degree. The procedure consumes the sum of the
scheduled lane lengths, divides the number of positions by their packing
product, and multiplies the leading energy coefficient by the quarter-bound
factor of Section 7.4.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {R : Type*} [CommSemiring R]

/-- Change the presentation of equal indices without changing the exact procedure. -/
def Procedure.reindex {a b k p a' b' k' p' : ℕ} {μ μ' : ℝ} (P : Procedure R a b k p μ)
    (ha : a = a') (hb : b = b') (hk : k = k') (hp : p = p') (hμ : μ = μ') :
    Procedure R a' b' k' p' μ' := ha ▸ hb ▸ hk ▸ hp ▸ hμ ▸ P

@[simp] theorem Procedure.error_reindex {a b k p a' b' k' p' : ℕ} {μ μ' : ℝ}
    (P : Procedure R a b k p μ) (ha : a = a') (hb : b = b') (hk : k = k')
    (hp : p = p') (hμ : μ = μ') : (P.reindex ha hb hk hp hμ).error = P.error := by
  subst a' b' k' p' μ'
  rfl

namespace BlockSchedule

variable {k : Type*} [Field k] (S : BlockSchedule k)

/-- One shrinking procedure per scheduled step, advancing to the next degree exponent with the
prescribed lane consumption, position divisor and shrinking energy multiplier. -/
abbrev ShrinkProcedures (R : Type*) [CommSemiring R] :=
  ∀ i : Fin S.steps, Procedure R (S.degreeExponent i.castSucc) (S.degreeExponent i.succ)
    (packingLaneBits (S.degreeExponent i.castSucc) 0)
    (packingFactor (S.degreeExponent i.castSucc)) shrinkMultiplier

/-- The final block procedure restoring the initial degree exponent, consuming the final
exponent in lane coordinates and preserving the number of positions with the scheduled
refresh multiplier. -/
abbrev RefreshProcedure (R : Type*) [CommSemiring R] :=
  Procedure R (S.degreeExponent (Fin.last S.steps)) (S.degreeExponent 0)
    (S.degreeExponent (Fin.last S.steps)) 1
    (refreshMultiplier S.baseDegree (2 ^ S.expanderExponent) S.poincare)

/-- The first `j` shrinking procedures in the fixed block. -/
noncomputable def shrinkPrefix (shrink : S.ShrinkProcedures R) (j : ℕ) (hj : j ≤ S.steps) :
    Procedure R (S.degreeExponent 0) (S.exponentAt j)
      (∑ i ∈ Finset.range j, packingLaneBits (S.exponentAt i) 0)
      (∏ i ∈ Finset.range j, packingFactor (S.exponentAt i)) (shrinkMultiplier ^ j) :=
  match j with
  | 0 => (Procedure.id R (S.degreeExponent 0)).reindex rfl
      (by unfold exponentAt; apply congrArg S.degreeExponent; ext; simp) (by simp) (by simp) (by simp)
  | j + 1 =>
    let i : Fin S.steps := ⟨j, hj⟩
    let previous := shrinkPrefix shrink j (by omega)
    let step := (shrink i).reindex (S.exponentAt_castSucc i).symm
      (show S.degreeExponent i.succ = S.exponentAt (j+1) by
        simp only [exponentAt, min_eq_left hj]; rfl)
      (congrArg (packingLaneBits · 0) (S.exponentAt_castSucc i).symm)
      (congrArg packingFactor (S.exponentAt_castSucc i).symm) rfl
    (previous.seq step).reindex rfl rfl (by rw [Finset.sum_range_succ])
      (by rw [Finset.prod_range_succ]) (by rw [pow_succ'])

/-- Run every shrinking procedure and then the refresh, keeping its exact
state execution for every possible term selection. -/
noncomputable def assembleBlock (shrink : S.ShrinkProcedures R) (refresh : S.RefreshProcedure R) :
    Procedure R (S.degreeExponent 0) (S.degreeExponent 0) S.laneBits S.positionFactor
      (refreshMultiplier S.baseDegree (2 ^ S.expanderExponent) S.poincare * shrinkMultiplier ^ S.steps) :=
  let all := (S.shrinkPrefix shrink S.steps le_rfl).reindex rfl
    (show S.exponentAt S.steps = S.degreeExponent (Fin.last S.steps) by
      simp only [exponentAt, min_self]; rfl) rfl rfl rfl
  (all.seq refresh).reindex rfl rfl
    (by simp only [laneBits, ← Fin.sum_univ_eq_sum_range, S.exponentAt_castSucc])
    (by simp only [positionFactor, ← Fin.prod_univ_eq_prod_range, S.exponentAt_castSucc, Nat.mul_one]) rfl

variable {R' : Type*} [CommSemiring R']

private theorem shrinkPrefix_error_congr (s : S.ShrinkProcedures R) (s' : S.ShrinkProcedures R')
    (hs : ∀ i, (s i).error = (s' i).error) (j : ℕ) (hj : j ≤ S.steps) :
    (S.shrinkPrefix s j hj).error = (S.shrinkPrefix s' j hj).error := by
  induction j with
  | zero =>
    rw [shrinkPrefix, shrinkPrefix]
    erw [Procedure.error_reindex]
  | succ j ih =>
    simp only [shrinkPrefix, Procedure.error_reindex, Procedure.seq, ih (Nat.le_of_succ_le hj), hs]

/-- When the constituent numerical bounds agree, the additive error of
the whole block agrees across coefficient rings and parameter assignments. -/
theorem assembleBlock_error_congr (s : S.ShrinkProcedures R) (s' : S.ShrinkProcedures R')
    (r : S.RefreshProcedure R) (r' : S.RefreshProcedure R')
    (hs : ∀ i, (s i).error = (s' i).error) (hr : r.error = r'.error) :
    (S.assembleBlock s r).error = (S.assembleBlock s' r').error := by
  unfold assembleBlock
  erw [Procedure.error_reindex, Procedure.error_reindex]
  simp only [Procedure.seq, Procedure.error_reindex, S.shrinkPrefix_error_congr s s' hs, hr]

end BlockSchedule
end Compression

end VPVNP
end Computability
end OAI

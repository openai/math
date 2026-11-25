import OAI.Hierarchy.ABPFirstCut
import OAI.Hierarchy.ABPFirstCutRegroup
import OAI.Hierarchy.SlotCoefficientClosure

namespace OAI
/-! # First-cut rank bounds for degree-component border ABPs

Selecting one variable per slot is a coordinate projection on the vector of
coefficients in the degree equal to the number of slots. Hence any polynomial
equation satisfied by the sums of low-rank first-cut tensors also vanishes on
the selected coefficient tensor of a border computation.
-/

namespace Hierarchy.ABPFirstCut

open MvPolynomial Computability.BorderVNP
open scoped BigOperators Classical
noncomputable section

variable {V : Type} {τ : V → Type} [Fintype V] {F : Type*} [Field F]

variable [DecidableEq V] [∀ i, Fintype (τ i)]

/-- Tensors admitting one summand per cut, of matrix rank at most `s` on
that particular cut. -/
def cutRankSums (family : Finset (Finset V)) (s : ℕ) : Set ((∀ i, τ i) → F) :=
  rankSumsOn (fun U : family => U.val) s

omit [Fintype V] [DecidableEq V] [∀ i, Fintype (τ i)] in
/-- Unused cut states can be given zero factors. -/
theorem CutFactorization.mono {family : Finset (Finset V)} {n m : ℕ}
    {T : (∀ i, τ i) → F} (h : CutFactorization family n T) (hnm : n ≤ m) :
    CutFactorization family m T := by
  induction hnm with
  | refl => exact h
  | step _ ih =>
    obtain ⟨L, R, heq⟩ := ih
    refine ⟨fun U => Fin.lastCases (fun _ => 0) (L U),
      fun U => Fin.lastCases (fun _ => 0) (R U), fun a => ?_⟩
    simpa [Fin.sum_univ_castSucc] using heq a

/-- Border computations give the closure of tensors with explicit factors on
both sides of every cut, sharing a cut-state index of size `s`. -/
theorem border_abp_first_cut_factors {f : MvPolynomial (Σ i, τ i) F} {s : ℕ}
    (family : Finset (Finset V)) (hempty : ∅ ∉ family) (hcover : HitsEveryOrder family)
    (h : DegreeBorderAtMost HasABP (Fintype.card V) s f) :
    (fun a => slotCoeff a Finset.univ (map (algebraMap F (AlgebraicClosure F)) f)) ∈
      imageClosure { T | CutFactorization family s T } := by
  apply degreeModelClosure_slots HasABP _ _ h
  rintro _ ⟨g, rfl, hs⟩
  exact (abp_first_cut g family hempty hcover).mono
    ((Nat.le_add_right g.vertices g.rows.edgeCount).trans hs)

/-- A border ABP puts the selected coefficients in the Zariski closure of
the sums of low-rank first-cut tensors, with the original size bound. -/
theorem border_abp_first_cut {f : MvPolynomial (Σ i, τ i) F} {s : ℕ}
    (family : Finset (Finset V)) (hempty : ∅ ∉ family) (hcover : HitsEveryOrder family)
    (h : DegreeBorderAtMost HasABP (Fintype.card V) s f) :
    (fun a => slotCoeff a Finset.univ (map (algebraMap F (AlgebraicClosure F)) f)) ∈
      imageClosure (cutRankSums family s) := by
  apply imageClosure_mono _ (border_abp_first_cut_factors family hempty hcover h)
  intro T hT
  exact CutFactorization.exists_summands hT

set_option maxHeartbeats 1000000 in
/-- After splitting the slots into their physical legs, each summand still has
rank at most `s` across all legs belonging to the summand's chosen slots. -/
theorem border_abp_first_cut_on_legs {P : Type} {ν : P → Type}
    [Fintype P] [DecidableEq P] [∀ p, Fintype (ν p)]
    (owner : P → V) (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    {f : MvPolynomial (Σ i, τ i) F} {s : ℕ} (family : Finset (Finset V))
    (hempty : ∅ ∉ family) (hcover : HitsEveryOrder family)
    (h : DegreeBorderAtMost HasABP (Fintype.card V) s f) :
    (fun x => slotCoeff (slotRead owner assemble x) Finset.univ
      (map (algebraMap F (AlgebraicClosure F)) f)) ∈
      imageClosure (rankSumsOn (fun U : family => legsOfCut owner U.val) s) :=
  closure_rankSumsOn_slotRead (F := AlgebraicClosure F) (τ := τ) (ν := ν)
    owner assemble (fun U : family => U.val) (s := s)
    (T := fun a => slotCoeff a Finset.univ (map (algebraMap F (AlgebraicClosure F)) f))
    (border_abp_first_cut (f := f) family hempty hcover h)


end
end Hierarchy.ABPFirstCut

end OAI

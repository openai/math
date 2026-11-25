import OAI.Computability.MultitapeWeakETH.EntropyPrice

/-! # Charging pin entropy to a point outside the placed network -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireTensor Finset MatrixMultiplication MatrixMultiplication.Foundation
open LabelHierarchyCounts StageHierarchyResources ConditionalLabels
open scoped Classical
noncomputable section

variable {K J E A : Type} [Field K] [Fintype J] [Fintype E] [Fintype A]

private def withRootBasis (a b : E → J) (I : E → Type) [∀ e, Fintype (I e)]
    (j : J) (ext : (wireNetwork (k:=K) (some ∘ a) (some ∘ b) I).Basis (some j)) :
    (wireNetwork (k:=K) a b I).Basis j :=
  (fun e h => ext.1 e (congrArg some h),fun e h => ext.2 e (congrArg some h))

omit [Fintype J] in
private theorem withRoot_support (a b : E → J) (I : E → Type) [∀ e, Fintype (I e)]
    (z : ∀ j, (wireNetwork (k:=K) (some ∘ a) (some ∘ b) I).Basis j) (value : (e : E) → I e) :
    (fun j => withRootBasis a b I j (z (some j))) = edgeAssignment a b value ↔
      z = edgeAssignment (some ∘ a) (some ∘ b) value := by
  refine ⟨fun eq => ?_,fun eq => by subst z; rfl⟩
  funext v
  apply Prod.ext
  · funext e h
    subst v
    exact congrFun (congrFun (congrArg Prod.fst (congrFun eq (a e))) e) rfl
  · funext e h
    subst v
    exact congrFun (congrFun (congrArg Prod.snd (congrFun eq (b e))) e) rfl

private def extraPin (Pin : J → Type) : Option J → Type
  | none => Unit
  | some j => Pin j

private instance (Pin : J → Type) [∀ j, Fintype (Pin j)] (j : Option J) : Fintype (extraPin Pin j) := by
  cases j <;> unfold extraPin <;> infer_instance

set_option maxHeartbeats 650000 in
/-- An isolated site at the geometric root has unit tensor and contributes zero
pin charge. This permits taking the barycenter of the placement as root. -/
theorem paired_entropy_external_root {X : Type} [PseudoMetricSpace X]
    (realizable : VPVNP.WireGeometry.RealizableConfigurations K X) (place : J → X) (root : X)
    (a b : E → J) (w : E → ℕ) (Pin : J → Type) [∀ j, Fintype (Pin j)] (pin : ∀ j, A → Pin j)
    (p : FiniteLaw A) (labels : ℕ → A → Bool) (depth : ℕ)
    (separate : Function.Injective (labelRecordOf labels depth)) (u v : Fin depth → J)
    (maps : ∀ j, Pin j → (wireNetwork (k:=K) u v (fun _ => Bool)).Basis j →
      (wireNetwork (k:=K) a b (fun e => Fin (2^w e))).Basis j → K)
    (scalar : A → K) (nz : ∀ x, scalar x ≠ 0)
    (display : ∀ x, applyLocal (fun j => maps j (pin j x))
      (wireNetwork a b (fun e => Fin (2^w e))).coeff =
      fun z => if z = edgeAssignment u v (fun j => labels j x) then scalar x else 0) :
    (∑ l : Fin depth, (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy l /
      Real.log 2 * dist (place (u l)) (place (v l))) ≤
      ∑ e, (w e:ℝ)*dist (place (a e)) (place (b e)) +
        ∑ j, finiteEntropy ((p.map (pin j)).mass)/Real.log 2 * dist root (place j) := by
  let extra (j : Option J) (x : A) : extraPin Pin j :=
    match j with | none => () | some k => pin k x
  let U := fun e => Fin (2^w e)
  let M (j : Option J) : extraPin Pin j →
      (wireNetwork (k:=K) (some ∘ u) (some ∘ v) (fun _ => Bool)).Basis j →
      (wireNetwork (k:=K) (some ∘ a) (some ∘ b) U).Basis j → K :=
    match j with
    | none => fun _ _ _ => 1
    | some k => fun t z y => maps k t (withRootBasis u v _ k z) (withRootBasis a b U k y)
  have showAt (x : A) : applyLocal (fun j => M j (extra j x))
      (wireNetwork (some ∘ a) (some ∘ b) U).coeff = fun z =>
        if z = edgeAssignment (some ∘ u) (some ∘ v) (fun l : Fin depth => labels l x) then scalar x else 0 := by
    funext z
    let old j := withRootBasis (K:=K) u v _ j (z (some j))
    have h := congrFun (display x) old
    rw [applyLocal_wireNetwork] at h ⊢
    simp only [Fintype.prod_option,M,extra,one_mul]
    apply h.trans
    have support := withRoot_support (K:=K) u v (fun _ => Bool) z (fun l => labels l x)
    split <;> rename_i condition
    · exact (ite_eq_left (support.mp condition)).symm
    · exact (ite_eq_right (fun eq => condition (support.mpr eq))).symm
  have bound := paired_entropy_at_placement realizable (fun j => j.elim root place) none
    (some ∘ a) (some ∘ b) w (extraPin Pin) extra p labels depth separate
    (some ∘ u) (some ∘ v) M scalar nz (by
      intro x
      apply (showAt x).trans
      funext z
      split <;> rfl)
  simp only [Fintype.sum_option,Function.comp_apply,Option.elim_some,Option.elim_none,dist_self,mul_zero,zero_add] at bound
  apply bound.trans_eq
  congr 1

end
end OAI.Computability.MultitapeWeakETH

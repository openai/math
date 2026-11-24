import OAI.Computability.VPVNP.LiveHeaderPaddingCount

/-!
# Incoming checks on the active branches

On a first-half or midpoint input the native header tests the incoming
padding directly. At a later incoming cut a nonzero transition count forces
a decodable configuration. Consequently, after both header scans succeed,
the native active branch may use the raw pair or transition count directly.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.Fields
open LiveHeaderSchedule LiveHeaderDescriptors LiveHeader ChainAssignments
open CutSchedule ExponentTrace LiveChain LiveEvaluatorEncoding
open scoped Classical

variable {s : Sizes} {t Z M w : ℕ} {E : UniversalMachine.Program}
variable {Nom : Type*} [Fintype Nom]
variable {Path : Exterior s.h s.delta → Fin (2^s.h) → Nom → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]

private theorem left_pairPadding {tag : Mode.Tag} (ev : tag ≠ Mode.Tag.unit) (he : s.e = t*Z) (hd : 0 < s.delta)
    {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {i : Fin (2^s.h)}
    (atCut : g.castSucc = firstCut i) (valid : ValidPadding s cuts g tag .left) :
    pairPadding t Z (liveCutEquiv s.h s.delta cuts).1 i := by
  have e : incidentCut .left g = firstCut i := atCut
  have hpos : 0 < (incidentCut .left g).val := e ▸ Nat.succ_pos _
  have hhalf : (incidentCut .left g).val ≤ 2^s.h := e ▸ i.isLt
  unfold ValidPadding at valid
  rw [interval_pair s g tag ev .left .padding hd hpos hhalf,he] at valid
  unfold incidentWidth at valid
  rw [e] at valid
  exact valid

private theorem left_decoded_of_count (layout : LiveEvaluatorTail.Layout E.extra M w s.delta)
    (initial : Code E.extra M) (bits : TailBits s.h s.delta) (k : Fin (2^s.h-1))
    (j : Fin (2^s.h)) (hj : j.val = k.val+1) (count : tailCount E layout initial bits j ≠ 0) :
    (LiveEvaluatorTail.readCut layout k (bits k)).isSome = true := by
  cases hr : LiveEvaluatorTail.readCut layout k (bits k) with
  | some v => rfl
  | none =>
    have hmid : LiveEvaluatorTail.boundary layout initial bits j.castSucc = none := by
      have h₀ : j.val ≠ 0 := by omega
      have hL : j.val ≠ 2^s.h := j.isLt.ne
      simp only [LiveEvaluatorTail.boundary,Fin.val_castSucc,h₀,hL,↓reduceDIte]
      have h : (⟨j.val-1,by have := j.isLt; omega⟩ : Fin (2^s.h-1)) = k := Fin.ext (by simp [hj])
      rw [h]; exact hr
    exfalso
    apply count
    unfold tailCount
    apply Finset.sum_eq_zero
    intro bit _
    apply ite_eq_right
    rintro ⟨a,b,ha,_⟩
    rw [hmid] at ha
    contradiction

/-- The potentially stronger incoming check contributes no further factor
once the physical padding passes and the active group's count is nonzero. -/
theorem incoming_of_active_nonzero {tag : Mode.Tag} (ev : tag ≠ .unit) (he : s.e = t*Z)
    (fit : 1+t*Z ≤ s.delta) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (layout : LiveEvaluatorTail.Layout E.extra M w s.delta) (init : (Fin t → ℕ) → Code E.extra M)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1)))
    (left : ValidPadding s cuts g tag .left) (count : groupEvaluation fit inc E layout init cuts g ≠ 0) :
    incomingChecks t Z layout cuts g := by
  rcases coverCuts g.castSucc with z | l | ⟨i,hi⟩ | ⟨k,hk⟩
  · exact incomingChecks_initial t Z layout cuts (congrArg Fin.val z)
  · exact (Fin.castSucc_ne_last g l).elim
  · exact (incomingChecks_pair t Z layout cuts i hi).2 (left_pairPadding ev he (by omega) hi left)
  · let j : Fin (2^s.h) := ⟨k.val+1,by have := k.isLt; omega⟩
    have same : g = halves s.h (.inr j) := Fin.ext (congrArg (fun v : Fin (2^(s.h+1)+1) => v.val) hk)
    rw [same] at count
    simp only [groupEvaluation,Equiv.symm_apply_apply,Sum.elim_inr] at count
    have hr := left_decoded_of_count layout _ _ k j rfl count
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hr
    exact (incomingChecks_tail t Z layout cuts k hk).2 ⟨x,(LiveEvaluatorTail.readCut_iff layout k _ x).1 hx⟩

theorem specified_eq_evaluation {tag : Mode.Tag} (ev : tag ≠ .unit) (he : s.e = t*Z)
    (fit : 1+t*Z ≤ s.delta) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (layout : LiveEvaluatorTail.Layout E.extra M w s.delta) (init : (Fin t → ℕ) → Code E.extra M)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1)))
    (selected : physicalTag cuts g = some tag) (left : ValidPadding s cuts g tag .left) :
    specifiedGroupCount fit inc E layout init cuts g = groupEvaluation fit inc E layout init cuts g := by
  rw [← routed_specifiedGroupCount fit inc E layout init cuts g s.e s.config,selected]
  cases tag with
  | unit => contradiction
  | pair | tail =>
    by_cases h : incomingChecks t Z layout cuts g
    · simp [routedCount,h]
    · have hz : groupEvaluation fit inc E layout init cuts g = 0 := by
        by_contra hn
        exact h (incoming_of_active_nonzero ev he fit inc layout init cuts g left hn)
      simp [routedCount,h,hz]

end LiveHeaderProgram.Fields

end VPVNP
end Computability
end OAI

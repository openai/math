import OAI.Computability.NearSquareRoot.PhysicalWalshCompileDispatchPlans
import OAI.Computability.NearSquareRoot.PrecisionEffectiveTemplate

/-! # A common effective selector for the physical and numerical Walsh kernels -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Dispatch

open IntegerMultiplication Code KernelPass KernelPass.ComputableSyntax PhysicalWalshNode
open PhysicalWalsh PhysicalWalshContext Pieces GeneratorSyntax CommonRegisters

/-- The executable family computes these dimensions directly from the literal
description used to emit the plan and its two recursive frames. -/
def dimensions (r : Raw) : ℕ × ℕ := (r.1-1,((ComputableSyntax.Shape.algebra r.1).parse r.2).1.1)

theorem primrec_dimensions : Primrec dimensions :=
  (Primrec.nat_sub.comp Primrec.fst (.const 1)).pair
    ((Primrec.fst.comp Primrec.fst).comp (ComputableSyntax.Shape.primrec_algebra.comp Primrec.fst Primrec.snd))

/-- Semantic certificates for the decoded plan at its two computed dimensions. -/
structure Selected (num den : ℕ) (r : Raw) where
  arity : r.1 = (dimensions r).1+1
  large : 5 ≤ (dimensions r).1+1
  wide : 2 ≤ (dimensions r).2
  plan : Plan ((dimensions r).1+1) (dimensions r).2 (dimensions r).2
  decode : Packed.decode ((dimensions r).1+1) r.2 = ⟨_,_,plan⟩
  correct : Correct plan
  saving : (plan.calls : ℝ) / (dimensions r).2 < (((dimensions r).1+1 : ℕ) : ℝ)^((num : ℝ)/den)
  precision : ∀ k ≥ rawPrecisionCutoff r, GroupedAccurateAt (a := (dimensions r).1)
    (by have := large; omega) (by have := wide; omega) plan k

/-- The decoded instruction list fixes the plan in every certificate. -/
theorem Selected.plan_eq {num den : ℕ} {r : Raw} (s t : Selected num den r) : s.plan = t.plan := by
  simpa only [Packed.mk.injEq, heq_eq_eq, true_and] using s.decode.symm.trans t.decode

instance {num den : ℕ} {r : Raw} : Subsingleton (Selected num den r) := by
  refine ⟨fun s t => ?_⟩
  have h := s.plan_eq t
  cases s
  cases t
  cases h
  rfl

/-- Every accepted search record has the stated dimensions and *that same*
plan enjoys the strict recursive saving and the working precision certificate. -/
theorem selected_of_good {num den : ℕ} (r : Raw) (hg : (interpreted r).Good num den) :
    Nonempty (Selected num den r) := by
  obtain ⟨a,W,ha,hw,p,hA,hP,hI,hc,hs,hk⟩ := accurateTemplate_of_good r hg
  have dA : (dimensions r).1 = a := by simp [dimensions,hA]
  have dW : (dimensions r).2 = W := by
    change ((ComputableSyntax.Shape.algebra r.1).parse r.2).1.1 = W
    rw [hA,←Packed.decode_shape,hP]
    rfl
  have geA := hg.1
  have geW := hg.2.1
  rw [hI] at geA geW
  change 5 ≤ a+1 at geA
  change 2 ≤ W at geW
  have H : ∀ (b v : ℕ), b = a → v = W → ∃ (plan : Plan (b+1) v v) (lar : 5 ≤ b+1) (wid : 2 ≤ v),
      Packed.decode (b+1) r.2 = ⟨v,v,plan⟩ ∧ Correct plan ∧
      (plan.calls : ℝ)/v < ((b+1 : ℕ) : ℝ)^((num : ℝ)/den) ∧
      ∀ k ≥ rawPrecisionCutoff r, GroupedAccurateAt (a:=b) (by omega) (by omega) plan k := by
    rintro _ _ rfl rfl
    exact ⟨p,geA,geW,hP,hc,hs,hk⟩
  obtain ⟨plan,lar,wid,eqn,corr,save,acc⟩ := H _ _ dA dW
  exact ⟨⟨by simpa only [dA] using hA,lar,wid,plan,eqn,corr,save,acc⟩⟩

/-- Compile the actual raw templates supplied by a computable selector. Their
acceptance proofs also certify the rounded Walsh plans used in the traces. -/
theorem midpointWithFor {Z : Type} [Primcodable Z] (s : ℕ → Raw) (hs : Computable s)
    (good : ∀ j, (interpreted (s j)).Good (j+3) (2*(j+2)))
    (flat : Z × Raw → Op → Cmd) (effective : Effective ltr (Function.uncurry flat))
    (N : ℕ) (within : ∀ raw op, Within N (flat raw op)) :
    ∃ (emit : Z × ℕ → Cmd) (R d : ℕ), Computable (dimensions ∘ s) ∧ Computable (rawPrecisionCutoff ∘ s) ∧
      Effective ltr emit ∧ 0 < R ∧ 1 ≤ d ∧ (∀ j, Within R (emit j)) ∧
      ∃ sel : (j : ℕ) → Selected (j+3) (2*(j+2)) (s j), ∀ (z : Z) (j : ℕ),
        let a := (dimensions (s j)).1
        let W := (dimensions (s j)).2
        ∀ (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ q, arena q ≤ scan q),
          (∀ q, allowance (a+1) d q ≤ arena q) →
          (∀ q, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) q ≤ arena q) →
          XorRuns (fun r => flat (z,r)) a W (s j).2 scan arena →
          Body (by have := (sel j).wide; change 0 < (dimensions (s j)).2; omega)
            (sel j).plan scan arena cost (emit (z,j)) := by
  obtain ⟨emit,R,d,ee,hR,hd,reg,run⟩ := plansWith flat effective N within
  let sel j := Classical.choice (selected_of_good (s j) (good j))
  refine ⟨fun k => emit (k.1,s k.2),R,d,primrec_dimensions.to_comp.comp hs,rawPrecisionCutoff_primrec.to_comp.comp hs,
    ee.comp (Computable.fst.pair (hs.comp Computable.snd)),hR,hd,fun k => reg (k.1,s k.2),sel,?_⟩
  intro z j
  dsimp only
  intro scan arena cost cap fit route
  let t := sel j
  have key : ((dimensions (s j)).1+1,(s j).2) = s j := Prod.ext t.arity.symm rfl
  have exec := run z _ _ (s j).2 (show 0 < (dimensions (s j)).2 by have := t.wide; omega)
    t.plan t.decode scan arena cost cap fit route
  rw [key] at exec
  exact exec

/-- On every candidate index the same symbolic search record selects the
source program, positive arity, batch width, numerical cutoff and rate.
Only the physical flat XOR for its valid non-diagonal instructions is an
external machine primitive. -/
theorem midpointWith {Z : Type} [Primcodable Z] (flat : Z × Raw → Op → Cmd) (effective : Effective ltr (Function.uncurry flat))
    (N : ℕ) (within : ∀ raw op, Within N (flat raw op)) :
    ∃ (s : ℕ → Raw) (emit : Z × ℕ → Cmd) (R d : ℕ), Computable s ∧
      Computable (dimensions ∘ s) ∧ Computable (rawPrecisionCutoff ∘ s) ∧
      Effective ltr emit ∧ 0 < R ∧ 1 ≤ d ∧ (∀ j, Within R (emit j)) ∧
      ∃ sel : (j : ℕ) → Selected (j+3) (2*(j+2)) (s j), ∀ (z : Z) (j : ℕ),
        let a := (dimensions (s j)).1
        let W := (dimensions (s j)).2
        ∀ (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ q, arena q ≤ scan q),
          (∀ q, allowance (a+1) d q ≤ arena q) →
          (∀ q, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) q ≤ arena q) →
          XorRuns (fun r => flat (z,r)) a W (s j).2 scan arena →
          Body (by have := (sel j).wide; change 0 < (dimensions (s j)).2; omega)
            (sel j).plan scan arena cost (emit (z,j)) := by
  obtain ⟨s,hs,good⟩ := computable_midpoint_templates
  obtain ⟨emit,R,d,h⟩ := midpointWithFor s hs good flat effective N within
  exact ⟨s,emit,R,d,hs,h⟩

/-- The selected physical and numerical template for a router without an external parameter. -/
theorem midpoint (flat : Raw → Op → Cmd) (effective : Effective ltr (Function.uncurry flat))
    (N : ℕ) (within : ∀ raw op, Within N (flat raw op)) :
    ∃ (s : ℕ → Raw) (emit : ℕ → Cmd) (R d : ℕ), Computable s ∧
      Computable (dimensions ∘ s) ∧ Computable (rawPrecisionCutoff ∘ s) ∧
      Effective ltr emit ∧ 0 < R ∧ 1 ≤ d ∧ (∀ j, Within R (emit j)) ∧
      ∃ sel : (j : ℕ) → Selected (j+3) (2*(j+2)) (s j), ∀ (j : ℕ),
        let a := (dimensions (s j)).1
        let W := (dimensions (s j)).2
        ∀ (scan arena : PhysicalWalshNode.Shape → ℕ) (cost : ∀ q, arena q ≤ scan q),
          (∀ q, allowance (a+1) d q ≤ arena q) →
          (∀ q, routeArena (coords a W) PhysicalWalshNode.Shape.w (Header.wire (a+1)) q ≤ arena q) →
          XorRuns flat a W (s j).2 scan arena →
          Body (by have := (sel j).wide; change 0 < (dimensions (s j)).2; omega)
            (sel j).plan scan arena cost (emit j) := by
  obtain ⟨s,emit,R,d,hs,hDim,hCut,he,hR,hd,hr,sel,run⟩ := midpointWith (Z:=Unit) (fun k => flat k.2)
    (PhysicalWalshCompile.ignoreParameter effective) N (fun k => within k.2)
  exact ⟨s,fun j => emit ((),j),R,d,hs,hDim,hCut,PhysicalWalshCompile.fixCommandParameter he (),
    hR,hd,fun j => hr ((),j),sel,run ()⟩

end PhysicalWalshCompile.Dispatch

end NearSquareRoot
end Computability
end OAI

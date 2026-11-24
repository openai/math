import OAI.Computability.VPVNP.RankQueryUniformResources
import OAI.Computability.VPVNP.MacaulayTargetBudgets
import OAI.Computability.VPVNP.RankCoordinateSliceTargets

/-! # Numerical premises of the canonical slice-coordinate reader -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.ConcreteResources

open Dispatch RadicalCertificate.MonomialIndex
open SliceMinors NativeReader

variable {F : Type} [Field F] [DecidableEq F] {t eqs : ℕ}

/-- Fits both rectangular orientations, both ordinary determinant roots and
every operation-specific target, with a common clock and a separate space
cap. The index width is also the width of the incoming evaluator ordinals. -/
structure CanonicalFits (Q : QueryData t eqs F) (d w v e live space time : ℕ) : Prop where
  rowShape : height Q+height Q+(height Q+width Q)*height Q+width Q+8 < 2^d
  columnShape : width Q+width Q+(width Q+height Q)*width Q+height Q+8 < 2^d
  orderShape : order Q+order Q+0+order Q+8 < 2^d
  orderBound : order Q ≤ 2^d
  rowFit : height Q < 2^w
  columnFit : width Q < 2^w
  orderFit : order Q < 2^w
  dimensionFit : Q.dimension < 2^w
  labelFit : t+1 < 2^w
  gramFit : Cursor.gramWidth d ≤ w
  widthThree : 3 ≤ w
  depthFit : d ≤ w
  rootFit : 2*d+6 ≤ w
  descriptorFit : (d+1)*widthFactor ≤ w
  childFit : (2*d+6+1)*widthFactor ≤ w
  wordLive : w ≤ live
  arityLive : t ≤ live
  scalarLive : max live (e*v) ≤ live
  liveSpace : live ≤ space
  target (op : QueryData.Operation t) (i : Fin Q.dimension) :
    PairCall.requiredWidth (targetArgs Q op i) ≤ w ∧
    TargetRead.clock w live e v (targetArgs Q op i) ≤ time ∧ TargetRead.space w live e v ≤ space

theorem canonicalFits {P : ReaderPlan} {Q : QueryData P.arity (P.equations+P.pins) F} (h : P.Covers Q)
    {w e v degree limb : ℕ} (hw : planWidth P ≤ w) (he : e ≤ degree) (hv : v ≤ limb) (sp ex : ℕ) :
    CanonicalFits Q (planDepth P) w v e (P.live degree limb w sp) (P.armSpace degree limb w sp)
      (P.readTime degree limb w sp ex) := by
  obtain ⟨_,_,_,hrow,hcol,horder,hr⟩ := plan_query_shapes h
  have hgram := (planWidth_covers P).1.trans hw
  have hwidth := (planWidth_covers P).2.trans hw
  obtain ⟨h₃,hd,hroot,hdesc,hchild,_⟩ := gramWidth_fits hgram
  have addr := Nat.pow_le_pow_right (by decide : 0 < 2) hd
  change height Q + height Q + (height Q + width Q)*height Q + width Q + 8 < 2^(planDepth P) at hrow
  change width Q + width Q + (width Q + height Q)*width Q + height Q + 8 < 2^(planDepth P) at hcol
  change order Q+order Q+0+order Q+8 < 2^(planDepth P) at horder
  have hheight : height Q < 2^w := (show height Q < 2^(planDepth P) by omega).trans_le addr
  have hwidthQ : width Q < 2^w := (show width Q < 2^(planDepth P) by omega).trans_le addr
  have horderQ : order Q < 2^w := (show order Q < 2^(planDepth P) by omega).trans_le addr
  have hdim : Q.dimension ≤ order Q := Nat.sub_le ..
  have pairFits := ExponentISA.indexFits (t := P.arity) (L := P.source) (D := P.column)
    (scale := P.scale) (mark := P.arity) (request := 0) (k₁ := 0) (k₂ := 0) (Nat.zero_le _) (Nat.zero_le _)
  have har : P.arity < 2^P.pairWidth := pairFits.1.arity_lt
  have pw : P.pairWidth+1 ≤ w := by unfold ReaderPlan.wordWidth at hwidth; omega
  have harity : P.arity+1 < 2^w := by
    apply Nat.lt_of_lt_of_le _ (Nat.pow_le_pow_right (by decide : 0 < 2) pw)
    rw [pow_succ]
    have := Nat.two_pow_pos P.pairWidth
    omega
  have hscale := Nat.mul_le_mul he hv
  have live : w ≤ P.live degree limb w sp ∧ P.arity ≤ P.live degree limb w sp ∧
      max (P.live degree limb w sp) (e*v) ≤ P.live degree limb w sp := by
    unfold ReaderPlan.live
    omega
  have room : P.live degree limb w sp ≤ P.armSpace degree limb w sp := by
    dsimp only [ReaderPlan.armSpace,MacaulayRead.Arms.transient]
    omega
  refine ⟨hrow,hcol,horder,hr,hheight,hwidthQ,horderQ,hdim.trans_lt horderQ,harity,hgram,h₃,hd,hroot,
    hdesc,hchild,live.1,live.2.1,live.2.2,room,?_⟩
  intro op i
  obtain ⟨ht,_,_,_,hc,hs⟩ := ReaderPlan.target_bounds h op (targetArgs Q op i) rfl rfl rfl rfl rfl he hv hwidth sp ex
  exact ⟨ht,hc,hs⟩

end RankQuery.Stack.Coordinate.ConcreteResources

end VPVNP
end Computability
end OAI

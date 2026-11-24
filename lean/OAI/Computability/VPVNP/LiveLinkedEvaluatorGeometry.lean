import OAI.Computability.VPVNP.LiveLinkedEvaluatorCount

/-!
# Physical allocation for the linked evaluator routes

The old and new evaluator banks follow the distributed-header buffers. Each has
exactly one word per control or tape field. The scratch region follows both
banks, so the same upper bound on the shadow base controls every address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages LiveEvaluatorEncoding LiveEvaluatorRAM
open LiveEvaluatorRAM.Schedule (callFuel)
open scoped Fin.CommRing

variable (G : PairStages.Group)

/-- The evaluator tape-window radius computed at this group's public geometry. -/
abbrev radius := G.constants.radius.eval G.g
/-- Number of words in a physical evaluator configuration at the group's window radius. -/
abbrev k := fieldWords (radius G)
/-- The first source bit cell used by the incoming or outgoing configuration gather. -/
abbrev cutSource (outgoing : Bool) := EvaluatorGather.operands G outgoing 0
/-- The shadow base, used as an upper bound for the evaluator configuration banks and
transition scratch. -/
abbrev limit := (Layout.shadow G.constants).eval G.g

/-- Ordered physical intervals in the real public operand bank. -/
structure Addresses : Prop where
  leftStart : G.addr.val < (cutSource G false).val
  rightStart : (cutSource G false).val + k G * G.w = (cutSource G true).val
  sourceEnd : (cutSource G true).val + k G * G.w ≤ (G.transitionPub 1).val
  lastFlag : G.addr.val < ((Router.last.data G.g G.lit) 0).val
  flagEnd : ((Router.last.data G.g G.lit) 0).val < (cutSource G false).val
  oldEnd : (G.transitionPub 1).val + k G = (G.transitionPub 2).val
  newEnd : (G.transitionPub 2).val + k G = (G.transitionPub 3).val
  scratchEnd : (G.transitionPub 3).val + 5 ≤ limit G
  radiusWord : (G.transitionPub 0).val = radius G
  widthWord (outgoing : Bool) : (EvaluatorGather.operands G outgoing 2).val = G.w
  countWord (outgoing : Bool) : (EvaluatorGather.operands G outgoing 3).val = k G

theorem addresses (fits : limit G < 2^G.w) : Addresses G := by
  let t := Layout.stageTag.eval G.g
  let f := (HeaderLayout.flag Layout.header .last).eval G.g
  let a := (HeaderLayout.config G.constants.lengths Layout.header .left).eval G.g
  let b := (HeaderLayout.config G.constants.lengths Layout.header .right).eval G.g
  let o := (Layout.oldState G.constants).eval G.g
  let n := (Layout.newState G.constants).eval G.g
  let s := (Layout.transitionScratch G.constants).eval G.g
  let W := 2^G.w
  have hk : G.constants.configWords.eval G.g = k G := rfl
  have hw : G.constants.lengths.config.eval G.g = k G * G.w := rfl
  have htf : t < f := by change t < t+1+9; omega
  have hfa : f < a := by
    simp only [a,f,HeaderLayout.config,HeaderLayout.exponent,HeaderLayout.exterior,HeaderLayout.advice,
      HeaderLayout.rightIndex,HeaderLayout.leftIndex,HeaderLayout.population,HeaderLayout.high,
      HeaderLayout.index,HeaderLayout.flag,eval_add]
    rw [show (9 : PublicExpr).eval G.g = 9 from rfl, show (15 : PublicExpr).eval G.g = 15 from rfl]; omega
  have hab : a+k G*G.w = b := rfl
  have hbo : b+k G*G.w ≤ o := by
    change b+k G*G.w ≤ b+G.constants.lengths.config.eval G.g+21+G.constants.labels.eval G.g
    rw [hw]; omega
  have hon : o+k G = n := rfl
  have hns : n+k G = s := rfl
  have hs : s+5 ≤ limit G := by
    change s+5 ≤ s+5+24+G.constants.prefixCapacity.eval G.g+G.constants.labels.eval G.g; omega
  have hkr : radius G < k G := by dsimp [k,fieldWords]; omega
  have hwidth := Nat.lt_two_pow_self (n := G.w)
  have val (x : ℕ) (hx : x < W) : (Fin.ofNat (2^G.w) x).val = x := Nat.mod_eq_of_lt hx
  have hlim : limit G < W := fits
  have tv : G.addr.val = t := val t (by omega)
  have av : (cutSource G false).val = a := val a (by omega)
  have bv : (cutSource G true).val = b := val b (by omega)
  have fv : ((Router.last.data G.g G.lit) 0).val = f := val f (by omega)
  have ov : (G.transitionPub 1).val = o := val o (by omega)
  have nv : (G.transitionPub 2).val = n := val n (by omega)
  have sv : (G.transitionPub 3).val = s := val s (by omega)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    val (radius G) (by omega), ?_, ?_⟩
  · intro out; cases out <;> exact val _ hwidth
  · intro out; cases out <;> exact val _ (by omega : k G < W)

/-- One global address fit and the table and burst sizes imply the native
transition and gather geometry, for the true length-dependent radius. -/
theorem geometryFit (fits : limit G < 2^G.w) (hw : 2 ≤ G.w) (states : G.evaluator.extra+2 ≤ 2^G.w)
    (rows : 9*G.evaluator.extra ≤ 2^G.w) (gather : 8*G.w+67 ≤ G.clock)
    (clock : callFuel G.evaluator ≤ G.clockAt Stage.transition) : GeometryFit G (radius G) := by
  obtain ⟨l,r,e,_,_,o,n,s,rad,_,_⟩ := addresses G fits
  have kcalls : k G = Schedule.calls (radius G) := LiveEvaluatorGroup.fieldWords_eq_calls _
  refine ⟨⟨hw,states,rows,rad,?_,?_,?_,Or.inl ?_,Or.inl ?_⟩,clock,Or.inl ?_,gather,Or.inl ?_,?_⟩
  all_goals try change (G.transitionPub 1).val + k G ≤ (G.transitionPub 2).val
  all_goals omega

theorem gatherFit (fits : limit G < 2^G.w) (hw : 2 ≤ G.w) (out : Bool) : EvaluatorGather.Fit G out (k G) := by
  obtain ⟨l,r,e,_,_,o,n,s,rad,wc,kc⟩ := addresses G fits
  have hk : 0 < k G := by dsimp [k,fieldWords]; omega
  refine ⟨hk,hw,wc out,kc out,?_,?_,Or.inl ?_,Or.inl ?_⟩
  all_goals cases out
  all_goals first | change (cutSource G _).val + k G*G.w ≤ _ | skip
  all_goals try change (G.transitionPub 1).val + k G ≤ 2^G.w
  all_goals try change (G.transitionPub 2).val + k G ≤ 2^G.w
  all_goals try change (cutSource G false).val+k G*G.w ≤ (G.transitionPub 1).val
  all_goals try change (cutSource G true).val+k G*G.w ≤ (G.transitionPub 2).val
  all_goals try change G.addr.val < (G.transitionPub 1).val
  all_goals try change G.addr.val < (G.transitionPub 2).val
  all_goals omega

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI

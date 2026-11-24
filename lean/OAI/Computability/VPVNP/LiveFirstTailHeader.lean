import OAI.Computability.VPVNP.LiveHeaderOutputFrame
import OAI.Computability.VPVNP.LiveProgramHeader
import OAI.Computability.VPVNP.LiveLinkedEvaluatorGeometry
import OAI.Computability.VPVNP.LiveProgramAdviceInputLayout

/-!
# The first evaluator group after the initial-state write

At the midpoint the incoming cut still uses the pair format. The first
tail group therefore receives the accumulated exponents and the copied
advice in their physical header arrays. The router and the state writer
touch only the stage tag and old control word, leaving every old tape cell
blank and both input arrays intact for the advice and input sweeps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.FirstTailHeader

open BurstRAM LiveEvaluatorInitialize LiveEvaluatorEncoding PairStages
open LiveHeaderProgram LiveHeaderSchedule LiveHeader LiveHeaderDescriptors
open ChainAssignments CutSchedule ExponentTrace
open scoped Fin.CommRing

variable (G : Group)

/-- The header dimensions evaluated at the physical group's constants and geometry. -/
abbrev size := Header.sizes G.constants G.g
/-- The group's evaluated number of exponent labels. -/
abbrev labelCount := G.constants.labels.eval G.g
/-- The group's evaluated digit width for each exponent. -/
abbrev exponentWidth := G.constants.Z.eval G.g
/-- The physical group index of the first evaluator group, at the start of the second half. -/
abbrev middle (G : Group) : Fin (2^((size G).h+1)) := halves (size G).h (.inr 0)

/-- The typed exponent field of the same midpoint cut used in
`groupEvaluation` and in the evaluator's initial code. -/
abbrev middleWords (cuts : AllCuts (size G).h (size G).delta)
    (fit : 1+labelCount G*exponentWidth G ≤ (size G).delta) :=
  counters fit (liveCutEquiv (size G).h (size G).delta cuts).1 (Fin.last (2^(size G).h))

variable {hw : 4 ≤ G.w} {m : Memory G.w}
variable {advice : Bits (size G).advice} {cuts : AllCuts (size G).h (size G).delta}

/-- The physical input bank is precisely the last vector of first-half
counters, including the low-endian order of the bits within each label. -/
theorem middle_bits (out : Output (size G) (Header.base G.g) G.g.d hw advice cuts (middle G) .tail m)
    (fit : 1+labelCount G*exponentWidth G ≤ (size G).delta) :
    ∀ q : Fin (labelCount G*exponentWidth G),
      m ((HeaderLayout.exponent G.constants.lengths Layout.header .left).eval G.g+q.val) =
        PrimedInputRAM.encodeBit G.w (RAMSerialization.arrayBits _ _ (middleWords G cuts fit) q) := by
  let s := size G
  let k : Fin (2^s.h) := ⟨2^s.h-1, by have := Nat.two_pow_pos s.h; omega⟩
  have hsucc : k.succ = Fin.last (2^s.h) := Fin.ext (by
    change (2^s.h-1)+1 = 2^s.h; have := Nat.two_pow_pos s.h; omega)
  have cut : incidentCut .left (middle G) = firstCut k := by
    apply Fin.ext
    change 2^s.h+(0 : Fin (2^s.h)).val = (2^s.h-1)+1
    rw [Fin.val_zero]
    have := Nat.two_pow_pos s.h
    omega
  have pos : 0 < (incidentCut .left (middle G)).val := by rw [cut]; exact Nat.succ_pos _
  have half : (incidentCut .left (middle G)).val ≤ 2^s.h := by rw [cut]; exact k.isLt
  have fields (j : Fin (2^(s.h+1)+1)) (hj : j = firstCut k) (lo : 0 < j.val) (hi : j.val ≤ 2^s.h) :
      (firstHalfLayout s.h s.delta j.val (labelCount G) (exponentWidth G) lo hi fit (cuts j)).2.2.1 =
        counters fit (liveCutEquiv s.h s.delta cuts).1 k.succ := by subst j; rfl
  obtain ⟨_, _, img⟩ := out.fieldImage
  have stored := img.pair_exponents (by decide) .left
    (rfl : s.e = labelCount G*exponentWidth G) fit pos half
  rw [fields _ cut pos half, hsucc] at stored
  intro q
  obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [RAMSerialization.arrayBits_at]
  have atBit := stored i b
  have hq : (finProdFinEquiv (i,b)).val = i.val*exponentWidth G+b.val := by
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [hq]
  exact atBit

/-- After the nonempty evaluator's first state write, all arrays consumed
by the packing and input stages are in their concrete program locations. -/
theorem prepared (out : Output (size G) (Header.base G.g) G.g.d hw advice cuts (middle G) .tail m)
    (fit : 1+labelCount G*exponentWidth G ≤ (size G).delta)
    (hlimit : (Layout.shadow G.constants).eval G.g < 2^G.w) (running : G.evaluator.extra ≠ 0) :
    let result := EvaluatorRoutes.putMemory G false m
    let cp := Advice.copyBank G.constants G.g
    G.tagged Stage.prefixLength result ∧
      (∀ j : Fin (size G).advice, result (((Advice.fp G.constants G.g) 0).val+j.val) =
        PrimedInputRAM.encodeBit G.w (advice j)) ∧
      (∀ q : Fin (labelCount G*exponentWidth G),
        result ((HeaderLayout.exponent G.constants.lengths Layout.header .left).eval G.g+q.val) =
          PrimedInputRAM.encodeBit G.w (RAMSerialization.arrayBits _ _ (middleWords G cuts fit) q)) ∧
      result (cp 1).val = Fin.ofNat _ (controlTag G.evaluator).val ∧
      ∀ k : Fin (fieldWords (cp 0).val), 0 < k.val → result ((cp 1).val+k.val) = 0 := by
  intro result cp
  let s := size G
  let hb := Header.base G.g
  let ad := adviceBase s hb
  let ex := exponentBase s hb .left
  let old := (Layout.oldState G.constants).eval G.g
  let t := 2^G.g.d
  have htad : t < ad := by
    simp only [ad, adviceBase, rightIndexBase, leftIndexBase, populationAddr, highAddr, indexBase, hb, Header.base, t]
    omega
  have hadex : ad+s.advice ≤ ex := by dsimp [ad, ex, exponentBase, exteriorBase]; omega
  have hexlim : ex+s.e ≤ LiveHeaderSchedule.limit s hb := by
    dsimp only [ex, LiveHeaderSchedule.limit, configBase, exponentBase]
    omega
  have hlimold : LiveHeaderSchedule.limit s hb ≤ old := by
    change LiveHeaderSchedule.limit s hb ≤ LiveHeaderSchedule.limit s hb+21+labelCount G
    omega
  have hfit : old < 2^G.w := by
    have h : old ≤ (Layout.shadow G.constants).eval G.g := by
      simp only [old, Layout.shadow, Layout.orderMap, Layout.packedPrefix, Layout.adviceFrames,
        Layout.transitionScratch, Layout.newState, eval_add]
      omega
    exact h.trans_lt hlimit
  have tagVal : G.addr.val = t := Nat.mod_eq_of_lt (by omega : t < 2^G.w)
  have advVal : ((Advice.fp G.constants G.g) 0).val = ad := Nat.mod_eq_of_lt (by omega : ad < 2^G.w)
  have stateVal : (cp 1).val = old := Nat.mod_eq_of_lt hfit
  have hend : EvaluatorSentinel.destination G false = Stage.prefixLength := by
    simp [EvaluatorSentinel.destination, running]
  have stateWord : EvaluatorSentinel.operands G false 1 = cp 1 := rfl
  have htagstate : G.addr.val < (cp 1).val := by omega
  have afterWrite : result = writeMemory (writeMemory (EvaluatorRoutes.retag G Stage.initialState m)
      (cp 1) (Fin.ofNat _ (controlTag G.evaluator).val)) G.addr (LiveStageLink.tagWord G.w Stage.prefixLength) := by
    change EvaluatorSentinel.transferred G false _ = _
    rw [EvaluatorSentinel.transferred, EvaluatorSentinel.put, stateWord, hend]
    rfl
  have unchanged (a : ℕ) (htag : G.addr.val < a) (hstate : a ≠ (cp 1).val) : result a = m a := by
    rw [afterWrite]
    simp only [EvaluatorRoutes.retag, writeMemory, ite_eq_right htag.ne', ite_eq_right hstate]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [afterWrite]
    exact (show writeMemory _ G.addr _ G.addr.val = _ by simp [writeMemory])
  · intro j
    have hj : j.val < s.advice := j.isLt
    rw [advVal, unchanged _ (by omega) (by omega)]
    exact out.adviceWords j
  · intro q
    change result (ex+q.val) = _
    have hq : q.val < s.e := q.isLt
    rw [unchanged _ (by omega) (by omega)]
    exact middle_bits G out fit q
  · rw [afterWrite]
    simp [writeMemory, htagstate.ne']
  · intro k hk
    rw [unchanged _ (by omega) (by omega)]
    exact out.fresh_after_limit _ (by omega : LiveHeaderSchedule.limit s hb ≤ (cp 1).val+k.val)

end LiveProgram.FirstTailHeader

end VPVNP
end Computability
end OAI

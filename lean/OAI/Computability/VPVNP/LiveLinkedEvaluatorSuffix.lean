import OAI.Computability.VPVNP.LiveProgramPrefixCopyRun
import OAI.Computability.VPVNP.LiveProgramSkeletonRun
import OAI.Computability.VPVNP.LiveProgramScatterRun
import OAI.Computability.VPVNP.LiveProgramAdviceInputLayout

/-!
# The linked midpoint prefix copy, skeleton generation and exponent scatter

All three calls read their operands from published frames. The only changes
outside the initialized tape bank are the stage transfers. The accepting
continuation therefore starts with the intended initial code and the tag
of the last-group router.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group

open BurstRAM LiveStageLink CompressorRecords LiveEvaluatorInitialize
open LiveEvaluatorReindex (Sources)
open EvaluatorProgramRawInput (runtime runtime_length)
open LiveEvaluatorEncoding (fieldWords)
open scoped Fin.CommRing

variable {d t Z : ℕ}

/-- The concrete suffix runs and its final evaluator bank. -/
structure SuffixRun (G : Group) (cp : Fin 4 → Word G.w) (raw : List Bool)
    (formal : Fin t → Word Z) (d : ℕ) (m final : Memory G.w) : Prop where
  returning : Advice.Returning G.P G.clock (max 1 raw.length + (2*(t*Z)+6*Z+4) + max 1 (d*Z)) 10 m final
  cost : Advice.CostLimit G.P G.clock (max 1 raw.length + (2*(t*Z)+6*Z+4) + max 1 (d*Z)) m
    (10*max 1 raw.length + 8*(2*(t*Z)+6*Z+4) + 11*max 1 (d*Z))
  config : LiveEvaluatorRAM.ConfigAt final (cp 1) (LiveEvaluatorTail.initialCode (cp 0).val
    (UniversalMachine.initial G.evaluator (raw ++ runtime formal)))
  tag : G.tagged Stage.last final
  outside (j : ℕ) (hTag : j ≠ G.addr.val) (hBank : j < (cp 1).val ∨ (cp 1).val + fieldWords (cp 0).val ≤ j) :
    final j = m j

/-- Static frame addresses and input banks lie outside the tape area being written. -/
structure SuffixRoom (G : Group) (cp : Fin 4 → Word G.w) (sc : Fin 5 → Word G.w) : Prop where
  tagState : G.addr.val < (cp 1).val
  tagInput : G.addr.val < (sc 0).val
  tagOrder : G.addr.val < (sc 1).val
  stateFit : (cp 1).val + fieldWords (cp 0).val ≤ 2^G.w
  prefixWord (i : Fin 5) : (cp 1).val + fieldWords (cp 0).val ≤ (G.prefixCopyBase + (i.val : Word G.w)).val
  skeleton (i : Fin 4) : (cp 1).val + fieldWords (cp 0).val ≤ (G.skeletonBase + (i.val : Word G.w)).val
  scatter (i : Fin 5) : (cp 1).val + fieldWords (cp 0).val ≤ (ScatterRun.operandBase G + (i.val : Word G.w)).val

/-- Execute the three framed native tables at their actual stage tags.
The initial control word has already been installed and the tape cells are
blank. -/
theorem suffixRun (G : Group) (cp sk state : Fin 4 → Word G.w) (sc : Fin 5 → Word G.w)
    (raw : List Bool) (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z) (formal : Fin t → Word Z)
    (order : ∀ i, formal (perm i) = dense i) (m : Memory G.w) (clock : 94 ≤ G.clock)
    (hw : 2 ≤ G.w) (running : G.evaluator.extra ≠ 0) (hs : G.evaluator.extra+2 ≤ 2^G.w)
    (L : LiveEvaluatorInputStages.Layout cp sk state sc d t Z raw.length)
    (room : SuffixRoom G cp sc) (space : raw.length+(2*(t*Z)+6*Z+4) ≤ (cp 0).val+1)
    (start : G.tagged Stage.prefixCopy m)
    (control : m (cp 1).val = Fin.ofNat _ (controlTag G.evaluator).val)
    (zeros : ∀ i : Fin (fieldWords (cp 0).val), 0 < i.val → m ((cp 1).val+i.val) = 0)
    (packed : ∀ j < raw.length, m (sourceAddress cp (j : Word G.w)).val = inputWord G.w raw (j/G.w))
    (src : Sources sc perm dense m) (cpData : Frame.data G.prefixCopyBase m = copyPublic cp (raw.length : Word G.w))
    (skData : Frame.data G.skeletonBase m = sk) (scData : Frame.data (ScatterRun.operandBase G) m = sc) :
    ∃ final, SuffixRun G cp raw formal d m final := by
  let zeroRuntime := runtime (fun _ : Fin t => (0 : Word Z))
  have hlen : zeroRuntime.length = 2*(t*Z)+6*Z+4 := runtime_length ..
  have hTag := room.tagState
  have hEnd : firstData cp + raw.length + zeroRuntime.length ≤ (cp 1).val + fieldWords (cp 0).val := by
    rw [hlen, firstData, fieldWords]; omega
  have hpre : G.addr.val < firstData cp := by unfold firstData; omega
  have hsk := L.runtimeBase
  obtain ⟨u, hu, copied⟩ := G.prefixCopyRun cp raw m hw L.wordWidth running L.prefixFit packed
    (fun j hj => (L.packedSeparate j hj).2) cpData start (.inl hpre)
    (fun j => .inr (by have := room.prefixWord j; omega)) (by omega)
  let m₁ := writeMemory u G.addr (tagWord G.w Stage.skeleton)
  have frame₁ : Frame.data G.skeletonBase m₁ = sk := by
    rw [← skData]
    funext j
    have hj := room.skeleton j
    change writeMemory u G.addr _ _ = _
    rw [writeMemory, ite_eq_right (by omega), copied.outside _ (.inr (by omega))]; rfl
  obtain ⟨v, hv, _, copied'⟩ := G.skeletonRun sk m₁ hw L.runtimeWidth L.runtimeBits L.runtimeLength L.runtimeFit
    frame₁ (by simp [tagged, m₁, writeMemory]) (.inl (by omega))
    (fun j => .inr (by rw [hsk, L.runtimeLength]; have := room.skeleton j; omega)) (by omega)
  let taggedInput := writeMemory m G.addr (tagWord G.w Stage.scatter)
  let taggedCopy := writeMemory u G.addr (tagWord G.w Stage.scatter)
  let m₂ := writeMemory v G.addr (tagWord G.w Stage.scatter)
  have hcopy : Copied raw (firstData cp) raw.length taggedInput taggedCopy :=
    copied_with_tag copied G.addr _ (.inl hpre)
  have hskel : Copied zeroRuntime (firstData cp + raw.length) zeroRuntime.length taggedCopy m₂ := by
    simpa only [m₁, Advice.write_tag_twice, taggedCopy, m₂, zeroRuntime, hsk] using copied'
  have both := hcopy.append hskel
  have agree (a : ℕ) (hne : a ≠ G.addr.val) (ho : a < firstData cp ∨ firstData cp+raw.length+zeroRuntime.length ≤ a) :
      m₂ a = m a := by
    have he := both.outside a (by simpa only [List.length_append, Nat.add_assoc] using ho)
    exact he.trans (ite_eq_right hne)
  have hsrc : Sources sc perm dense m₂ := by
    constructor
    · intro j
      have hp := L.incomingSeparate j
      have he := agree ((sc 0).val+j.val) (by have := room.tagInput; omega) (by rw [hlen]; simpa only [L.runtimeLength] using hp.2)
      rw [he, src.incoming]
    · intro j
      have hp := L.mapSeparate j
      have he := agree ((sc 1).val+j.val) (by have := room.tagOrder; omega) (by rw [hlen]; simpa only [L.runtimeLength] using hp.2)
      rw [he, src.order]
  have frame₂ : Frame.data (ScatterRun.operandBase G) m₂ = sc := by
    rw [← scData]
    funext j
    have hj := room.scatter j
    exact agree _ (by omega) (.inr (by omega))
  let blank := writeMemory taggedInput (cp 1) 0
  have hz : ∀ i : Fin (fieldWords (cp 0).val), blank ((cp 1).val+i.val) = 0 := by
    intro i
    by_cases he : i.val = 0
    · simp [blank, writeMemory, he]
    · simp only [blank, taggedInput, writeMemory, ite_eq_right (by omega : (cp 1).val+i.val ≠ (cp 1).val),
        ite_eq_right (by omega : (cp 1).val+i.val ≠ G.addr.val), zeros i (by omega)]
  have hcontrol : writeMemory blank (cp 1) (Fin.ofNat _ (controlTag G.evaluator).val) = taggedInput := by
    rw [show blank = _ from rfl, Advice.write_tag_twice]
    funext j
    by_cases he : j = (cp 1).val
    · subst j; simp [taggedInput, writeMemory, show (cp 1).val ≠ G.addr.val by omega, control]
    · simp [writeMemory, he]
  have prepared := prefix_runtime_stores (t := t) (Z := Z) hw cp G.evaluator running hs raw blank taggedCopy m₂
    (by simpa only [List.length_append, runtime_length] using space) hz (hcontrol ▸ hcopy)
    (by simpa only [zeroRuntime, runtime_length] using hskel)
  have hscl : (sc 2).val + 2*(sc 4).val ≤ (cp 1).val+fieldWords (cp 0).val := by
    rw [L.scatter.target, L.scatter.total, fieldWords]; omega
  obtain ⟨final, hret, _, hconfig, tag, cost, keep⟩ := ScatterRun.returning_outside G clock hw sc perm dense formal order
    running hs raw (cp 1) (cp 0).val L.scatter m₂ hsrc (by simpa only [List.length_append, runtime_length] using space)
    prepared (by simp [tagged, m₂, writeMemory]) frame₂
    (fun j => .inr (hscl.trans (room.scatter j))) (.inl room.tagState) room.stateFit
  change Advice.Returning G.P G.clock zeroRuntime.length 7 m₁ m₂ at hv
  rw [hlen] at hv
  have firstTwo := Advice.returning_append hu hv
  refine ⟨final, Advice.returning_append firstTwo hret,
    Advice.costLimit_append firstTwo hret
      (Advice.costLimit_append hu hv (Advice.returning_cost hu) (Advice.returning_cost hv)) cost, hconfig, tag, ?_⟩
  intro j ht hb
  have hbase : (cp 1).val ≤ firstData cp := by unfold firstData; omega
  have htarget : (cp 1).val ≤ (sc 2).val := by rw [L.scatter.target]; omega
  exact (keep j ht (by unfold ScatterRun.Outside; omega)).trans (agree j ht (by omega))

/-- Removing the unique complete suffix prefix preserves the full accepting
continuation and its cap on the concatenated event log. -/
noncomputable def SuffixRun.suffixEquiv {G : Group} {cp : Fin 4 → Word G.w} {raw : List Bool}
    {formal : Fin t → Word Z} {d : ℕ} {m final : Memory G.w} (h : SuffixRun G cp raw formal d m final)
    (cap : List (Report G.w) → Prop) :
    ActualPaths G.P G.clock 0 final (fun rs => cap (h.returning.choose ++ rs)) ≃ ActualPaths G.P G.clock 0 m cap := by
  have hr := h.returning.choose_spec
  have e := emptySegmentEquiv hr.1 cap
  rw [hr.2.1, hr.2.2.1] at e
  exact e

open Advice

/-- The physical midpoint program uses the three published operand rows of
the validated advice. Its old-state bank is the exact bounded initial code
on the complete raw prefix and formal exponents at the last-group router. -/
theorem suffixRun_actual (G : Group) (raw : List Bool) (m : Memory G.w)
    (values : Fin (G.constants.labels.eval G.g) → Word (Nat.clog 2 (G.constants.labels.eval G.g)))
    (perm : Fin (G.constants.labels.eval G.g) ≃ Fin (G.constants.labels.eval G.g))
    (dense formal : Fin (G.constants.labels.eval G.g) → Word (G.constants.Z.eval G.g))
    (order : ∀ i, formal (perm i) = dense i) (ordinal : ∀ i, (values i).val = (perm i).val)
    (L : LiveEvaluatorAdviceBanks.PreparedLayout (lp G.constants G.g) (fp G.constants G.g)
      (op G.constants G.g) raw (G.constants.labels.eval G.g) (Nat.clog 2 (G.constants.labels.eval G.g)))
    (hlimit : (Layout.shadow G.constants).eval G.g < 2^G.w) (clock : 94 ≤ G.clock)
    (running : G.evaluator.extra ≠ 0) (hs : G.evaluator.extra+2 ≤ 2^G.w)
    (space : raw.length + (2*(G.constants.labels.eval G.g*G.constants.Z.eval G.g)+6*G.constants.Z.eval G.g+4) ≤
      G.constants.radius.eval G.g+1)
    (incoming : ∀ q : Fin (G.constants.labels.eval G.g*G.constants.Z.eval G.g),
      m ((HeaderLayout.exponent G.constants.lengths Layout.header .left).eval G.g+q.val) =
        PrimedInputRAM.encodeBit G.w (RAMSerialization.arrayBits _ _ dense q))
    (control : m ((copyBank G.constants G.g) 1).val = Fin.ofNat _ (controlTag G.evaluator).val)
    (zeros : ∀ i : Fin (fieldWords (G.constants.radius.eval G.g)), 0 < i.val →
      m (((copyBank G.constants G.g) 1).val+i.val) = 0) :
    ∃ final, SuffixRun G (copyBank G.constants G.g) raw formal (G.constants.labels.eval G.g)
      (finalMemory G.constants G.g G.lit raw values m) final := by
  let c := G.constants
  let g := G.g
  let cp := copyBank c g
  let sk := skeletonBank c g raw m
  let sc := scatterBank c g raw m
  let base := (fp c g) 3
  let entry := finalMemory c g G.lit raw values m
  have R := inputRegions c g raw m L hlimit space
  have I := inputLayout c g raw m L hlimit space
  obtain ⟨hdc, hds, hda⟩ := suffixFrameData c g G.lit raw values m L hlimit
  obtain ⟨hpacked, hsrc, hframe⟩ := preparedInput c g G.lit raw values m L hlimit space perm dense ordinal incoming
  have addr (offset : ℕ) : Pieces.word g G.lit (.geometry (Layout.adviceFrames c + (.lit offset : PublicExpr))) =
      base + (offset : Word G.w) := by
    change (((Layout.adviceFrames c).eval g + offset : ℕ) : Word G.w) = (((Layout.adviceFrames c).eval g : ℕ) : Word G.w) + _
    exact Nat.cast_add ..
  have hc : G.prefixCopyBase = base + 8 := addr 8
  have hk : G.skeletonBase = base + 13 := addr 13
  have ha : ScatterRun.operandBase G = base + 17 := addr 17
  have before : base.val+23 ≤ ((fp c g) 4).val := L.frameBeforePrefix
  have hfit : base.val+22 < 2^g.w := (Nat.le_succ _).trans_lt (before.trans_lt ((fp c g) 4).isLt)
  have words {n : ℕ} (offset : ℕ) (j : Fin n) (h : offset + n ≤ 22) :
      base.val ≤ ((base + (offset : Word G.w)) + (j.val : Word G.w)).val := by
    have ho : offset < 2^g.w := by have := j.isLt; omega
    have hj : j.val < 2^g.w := by have := j.isLt; omega
    rw [Fin.val_add, Fin.val_add, Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hj,
      Nat.mod_eq_of_lt (by omega : base.val+offset < 2^g.w), Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    omega
  have ht : G.addr.val < ((fp c g) 0).val := tag_before_advice c g G.lit hlimit
  have htin : G.addr.val < (sc 0).val := ht.trans_le R.incomingStart
  have hts : G.addr.val < (cp 1).val := htin.trans_le ((Nat.le_add_right ..).trans R.incomingEnd)
  have hend : (cp 1).val + fieldWords (cp 0).val ≤ base.val := by rw [show (cp 0).val = _ from R.radius]; exact R.configEnd
  have hto : G.addr.val < (sc 1).val := by
    change G.addr.val < ((fp c g) 10).val
    rw [← L.ordinalDest]
    have hb : ((fp c g) 4).val ≤ ((op c g) 1).val := (Nat.le_add_right ..).trans L.prefixBeforeOrder
    exact hts.trans_le (((Nat.le_add_right ..).trans hend).trans (((Nat.le_add_right ..).trans before).trans hb))
  have room : SuffixRoom G cp sc := ⟨hts, htin, hto, hend.trans base.isLt.le,
    fun j => hc ▸ hend.trans (words 8 j (by decide)), fun j => hk ▸ hend.trans (words 13 j (by decide)),
    fun j => ha ▸ hend.trans (words 17 j (by decide))⟩
  have old : ∀ i : Fin (fieldWords (cp 0).val), entry ((cp 1).val+i.val) = m ((cp 1).val+i.val) :=
    fun i => hframe ⟨i.val, by simpa only [show (cp 0).val = _ from R.radius] using i.isLt⟩
  have hzero : ∀ i : Fin (fieldWords (cp 0).val), 0 < i.val → entry ((cp 1).val+i.val) = 0 := by
    intro i hi
    rw [old]
    exact zeros ⟨i.val, by simpa only [show (cp 0).val = _ from R.radius] using i.isLt⟩ hi
  have hctrl : entry (cp 1).val = Fin.ofNat _ (controlTag G.evaluator).val := by
    have hz := old ⟨0, by unfold fieldWords; omega⟩
    exact hz.trans control
  exact G.suffixRun cp sk (stateBank c g) sc raw perm dense formal order entry clock
    ((by decide : 2 ≤ 4).trans L.width) running hs I room (by rw [show (cp 0).val = _ from R.radius]; exact space)
    (by change (if G.addr.val = G.addr.val then _ else _) = _; rw [ite_eq_left rfl])
    hctrl hzero hpacked hsrc (hc ▸ hdc) (hk ▸ hds) (ha ▸ hda)

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI

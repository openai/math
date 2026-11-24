import OAI.Computability.VPVNP.LiveProgramAdviceRun
import OAI.Computability.VPVNP.LiveEvaluatorInputStages

/-!
# The live program's midpoint tape layout

The old state bank contains a head-relative two-tape window. The raw prefix
starts at its central cell, followed immediately by the evaluator runtime
fields. All scatter sources lie in the earlier header workspace, and the
permutation lookup table lies beyond both configuration banks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Advice

open BurstRAM (Word Memory)
open LiveEvaluatorAdviceFrames LiveEvaluatorAdviceBanks
open LiveEvaluatorInitialize (firstData sourceAddress inputWord)
open scoped Fin.CommRing

/-- The four fixed prefix-copy operands, in order the tape radius, old state base, packed
prefix base and word width. -/
def copyBank (c : Constants) (g : Geometry) : Fin 4 → Word g.w :=
  let f := fp c g
  ![f 5,f 6,f 4,f 2]

/-- Evaluated control-state operands that target the old evaluator configuration bank. -/
def stateBank (c : Constants) (g : Geometry) :=
  bank g (StageOperands.control c (Layout.oldState c))

/-- Memory after the length packer has stored the active raw prefix's length. -/
abbrev initialLengthMemory (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w) :=
  lengthMemory (lp c g) raw m

/-- The four runtime-skeleton operands evaluated using the stored prefix length, including the
suffix start and size. -/
def skeletonBank (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w) :=
  skeletonFrame (fp c g) (initialLengthMemory c g raw m)

/-- The five operands of the exponent scatter, with its tape destination determined from the
stored prefix length. -/
def scatterBank (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w) :=
  scatterFrame (fp c g) (initialLengthMemory c g raw m)

/-- Address order and exact words supplied to the subsequent three stages. -/
structure InputRegions (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w) : Prop where
  radius : (copyBank c g 0).val = c.radius.eval g
  state : (copyBank c g 1).val = (Layout.oldState c).eval g
  exponentWidth : (skeletonBank c g raw m 0).val = c.Z.eval g
  exponentBits : (skeletonBank c g raw m 1).val = c.labels.eval g*c.Z.eval g
  runtime : (skeletonBank c g raw m 2).val = firstData (copyBank c g) + raw.length
  runtimeSize : (skeletonBank c g raw m 3).val = 2*(c.labels.eval g*c.Z.eval g)+6*c.Z.eval g+4
  scatterStart : (scatterBank c g raw m 2).val = firstData (copyBank c g) + raw.length + (2*c.Z.eval g+1)+1
  incoming : (scatterBank c g raw m 0).val = (HeaderLayout.exponent c.lengths Layout.header .left).eval g
  incomingStart : ((fp c g) 0).val ≤ (scatterBank c g raw m 0).val
  incomingEnd : (scatterBank c g raw m 0).val + c.labels.eval g*c.Z.eval g ≤ (copyBank c g 1).val
  configEnd : (copyBank c g 1).val + LiveEvaluatorEncoding.fieldWords (c.radius.eval g) ≤ ((fp c g) 3).val

theorem inputRegions (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)))
    (hlimit : (Layout.shadow c).eval g < 2^g.w)
    (hspace : raw.length + (2*(c.labels.eval g*c.Z.eval g)+6*c.Z.eval g+4) ≤ c.radius.eval g+1) :
    InputRegions c g raw m := by
  let M := c.radius.eval g
  let Z := c.Z.eval g
  let t := c.labels.eval g
  let N := t*Z
  let state := (Layout.oldState c).eval g
  let incoming := (HeaderLayout.exponent c.lengths Layout.header .left).eval g
  let source := (HeaderLayout.advice c.lengths Layout.header).eval g
  let frame := (Layout.adviceFrames c).eval g
  let f := fp c g
  let u := initialLengthMemory c g raw m
  change raw.length+(2*N+6*Z+4) ≤ M+1 at hspace
  have src_order : source ≤ incoming := by
    simp only [source,incoming,HeaderLayout.exponent,HeaderLayout.exterior,eval_add]; omega
  have inp_order : incoming + N ≤ state := by
    have hh : incoming+N ≤ (HeaderLayout.limit c.lengths Layout.header).eval g := by
      change (HeaderLayout.exponent c.lengths Layout.header .left).eval g + c.lengths.e.eval g ≤ _
      simp only [HeaderLayout.limit,HeaderLayout.config,HeaderLayout.exponent,HeaderLayout.exterior,eval_add]
      omega
    exact hh.trans (by simp only [state,Layout.oldState,Layout.counter,Layout.descriptor,eval_add]; omega)
  have fieldEnd : state+(1+(2*M+1)+(2*M+1)) ≤ frame := by
    change (Layout.oldState c).eval g+c.configWords.eval g ≤ _
    simp only [frame,Layout.adviceFrames,Layout.transitionScratch,Layout.newState,eval_add]; omega
  have frameFit : frame < 2^g.w := by
    change (Layout.adviceFrames c).eval g < _
    simp only [Layout.shadow,Layout.orderMap,Layout.packedPrefix,eval_add] at hlimit
    omega
  have val (x : ℕ) (h : x < 2^g.w) : (Fin.ofNat (2^g.w) x).val = x := Nat.mod_eq_of_lt h
  have f0 : (f 0).val = source := val source (by omega)
  have f3 : (f 3).val = frame := val frame frameFit
  have f5 : (f 5).val = M := val M (by omega)
  have f6 : (f 6).val = state := val state (by omega)
  have f7 : (f 7).val = Z := val Z (by omega)
  have f8 : (f 8).val = N := val N (by omega)
  have f9 : (f 9).val = incoming := val incoming (by omega)
  have ha : (actualLength f u).val = raw.length := prepared_length L m
  have h16 : 16 ≤ 2^g.w := Nat.pow_le_pow_right (by decide : 0 < 2) L.width
  have v1 : (1 : Word g.w).val = 1 := val 1 (by omega)
  have v2 : (2 : Word g.w).val = 2 := val 2 (by omega)
  have v4 : (4 : Word g.w).val = 4 := val 4 (by omega)
  have v6 : (6 : Word g.w).val = 6 := val 6 (by omega)
  have hrun : (runtimeBase f u).val = state+1+M+raw.length := by
    simp only [runtimeBase,Fin.val_add,Nat.mod_add_mod,f5,f6,v1,ha]
    exact Nat.mod_eq_of_lt (by omega)
  have hsize : (skeletonSize f).val = 2*N+6*Z+4 := by
    simp only [skeletonSize,Fin.val_add,Fin.val_mul,Nat.mod_add_mod,Nat.add_mod_mod,f7,f8,v2,v4,v6]
    exact Nat.mod_eq_of_lt (by omega)
  have hscat : (scatterBase f u).val = state+1+M+raw.length+(2*Z+1)+1 := by
    simp only [scatterBase,Fin.val_add,Fin.val_mul,Nat.mod_add_mod,Nat.add_mod_mod,hrun,f7,v2]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  constructor
  · exact f5
  · exact f6
  · exact f7
  · exact f8
  · change (runtimeBase f u).val = (f 6).val+1+(f 5).val+raw.length
    rwa [f6,f5]
  · exact hsize
  · change (scatterBase f u).val = (f 6).val+1+(f 5).val+raw.length+(2*Z+1)+1
    rwa [f6,f5]
  · exact f9
  · change (f 0).val ≤ (f 9).val; rwa [f0,f9]
  · change (f 9).val + N ≤ (f 6).val; rwa [f9,f6]
  · change (f 6).val+(1+(2*M+1)+(2*M+1)) ≤ (f 3).val; rwa [f6,f3]

private theorem prefixSource (c : Constants) (g : Geometry) (raw : List Bool) (j : ℕ) (hj : j < raw.length)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g))) :
    (sourceAddress (copyBank c g) (j : Word g.w)).val = ((fp c g) 4).val+j/g.w ∧
    j/g.w < raw.length ⌈/⌉ g.w := by
  have hw : 0 < g.w := by have := L.width; omega
  have ha : raw.length ≤ g.w*(raw.length ⌈/⌉ g.w) := (ceilDiv_le_iff_le_mul hw).mp le_rfl
  have hr : j/g.w < raw.length ⌈/⌉ g.w := (Nat.div_lt_iff_lt_mul hw).mpr (hj.trans_le (by rwa [Nat.mul_comm]))
  have hjw := Fin.val_cast_of_lt (hj.trans_le L.rawFits |>.trans ((fp c g) 1).isLt)
  refine ⟨?_,hr⟩
  have hsum : ((fp c g) 4).val+j/g.w < 2^g.w := by
    have h := L.prefixBeforeOrder
    have h' := ((op c g) 1).isLt
    omega
  simp only [sourceAddress,Fin.val_add,Fin.val_ofNat,hjw,Nat.add_mod_mod]
  exact Nat.mod_eq_of_lt hsum

/-- All capacities and nonaliasing conditions for prefix copy, skeleton and
scatter on the three published operand banks. -/
theorem inputLayout (c : Constants) (g : Geometry) (raw : List Bool) (m : Memory g.w)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)))
    (hlimit : (Layout.shadow c).eval g < 2^g.w)
    (hspace : raw.length + (2*(c.labels.eval g*c.Z.eval g)+6*c.Z.eval g+4) ≤ c.radius.eval g+1) :
    LiveEvaluatorInputStages.Layout (copyBank c g) (skeletonBank c g raw m) (stateBank c g)
      (scatterBank c g raw m) (c.labels.eval g) (c.labels.eval g) (c.Z.eval g) raw.length := by
  let cp := copyBank c g
  let sk := skeletonBank c g raw m
  let sc := scatterBank c g raw m
  let f := fp c g
  let M := c.radius.eval g
  let Z := c.Z.eval g
  let N := c.labels.eval g*Z
  have R := inputRegions c g raw m L hlimit hspace
  change raw.length+(2*N+6*Z+4) ≤ M+1 at hspace
  have hd : firstData cp = (cp 1).val+1+M := by rw [firstData,R.radius]
  have he : (cp 1).val+(1+(2*M+1)+(2*M+1)) ≤ (f 3).val := R.configEnd
  have hf : (f 3).val+23 ≤ (f 4).val := L.frameBeforePrefix
  have hm : (f 4).val + (raw.length ⌈/⌉ g.w) ≤ (sc 1).val := L.prefixBeforeOrder
  have hi : (sc 0).val+N ≤ (cp 1).val := R.incomingEnd
  have hb : (sk 2).val = firstData cp+raw.length := R.runtime
  have hl : (sk 3).val = 2*N+6*Z+4 := R.runtimeSize
  have hs : (sc 2).val = firstData cp+raw.length+(2*Z+1)+1 := R.scatterStart
  have hw := (f 3).isLt
  have hsep : firstData cp+raw.length+(sk 3).val ≤ (f 3).val := by omega
  change LiveEvaluatorInputStages.Layout cp sk _ sc _ _ Z _
  constructor
  · rfl
  · exact L.frameWidth
  · omega
  · intro j hj
    have hx : (sourceAddress cp (j : Word g.w)).val = (f 4).val + j/g.w := (prefixSource c g raw j hj L).1
    change (sourceAddress cp (j : Word g.w)).val ≠ (cp 1).val ∧
      ((sourceAddress cp (j : Word g.w)).val < firstData cp ∨
        firstData cp+raw.length ≤ (sourceAddress cp (j : Word g.w)).val)
    rw [hx]
    have lower : (f 4).val ≤ (f 4).val+j/g.w := Nat.le_add_right ..
    exact ⟨(lt_of_lt_of_le (show (cp 1).val < (f 4).val by omega) lower).ne',
      Or.inr ((show firstData cp+raw.length ≤ (f 4).val by omega).trans lower)⟩
  · exact R.exponentWidth
  · exact R.exponentBits
  · exact hb
  · exact hl
  · omega
  · exact ⟨R.exponentWidth,R.exponentBits,by rw [hs,hd,R.radius],by omega,L.orderFit,by omega,
      Or.inl (by omega),Or.inr (by omega)⟩
  · intro q
    have hq : q.val < N := q.isLt
    dsimp only
    exact ⟨by omega,Or.inl (by omega)⟩
  · intro i
    dsimp only
    exact ⟨by omega,Or.inr (by omega)⟩


/-- In particular the four stages do not touch the old configuration or the
header's incoming exponent bank between the reserved tag and frame base. -/
theorem beforeFrame_preserved (c : Constants) (g : Geometry) (lit : LiteralPrefix) (raw : List Bool)
    (values : Fin (c.labels.eval g) → Word (Nat.clog 2 (c.labels.eval g))) (m : Memory g.w)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)))
    (hlimit : (Layout.shadow c).eval g < 2^g.w) (k : ℕ)
    (htag : (tagAddr g lit).val < k) (hbefore : k < ((fp c g) 3).val) :
    finalMemory c g lit raw values m k = m k := by
  have h := finalImage c g lit raw values m L hlimit
  have hf := L.frameBeforePrefix
  have ho := L.prefixBeforeOrder
  rw [h.outside k (.inl hbefore) (.inl (by omega)) (.inl (by omega)), BurstRAM.writeMemory,
    ite_eq_right (by omega)]

/-- Every physical operand loader in the final three middle stages reads the
four- or five-word bank computed from the validated raw length. -/
theorem suffixFrameData (c : Constants) (g : Geometry) (lit : LiteralPrefix) (raw : List Bool)
    (values : Fin (c.labels.eval g) → Word (Nat.clog 2 (c.labels.eval g))) (m : Memory g.w)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)))
    (hlimit : (Layout.shadow c).eval g < 2^g.w) :
    let out := finalMemory c g lit raw values m
    let base := (fp c g) 3
    CompressorRecords.Frame.data (base+8) out = LiveEvaluatorInitialize.copyPublic (copyBank c g) (raw.length : Word g.w) ∧
    CompressorRecords.Frame.data (base+13) out = skeletonBank c g raw m ∧
    CompressorRecords.Frame.data (base+17) out = scatterBank c g raw m := by
  let f := fp c g
  let u := initialLengthMemory c g raw m
  let mt := BurstRAM.writeMemory m (tagAddr g lit) (LiveStageLink.tagWord g.w Stage.prefixCopy)
  let v := initialLengthMemory c g raw mt
  have hf : (f 3).val+23 ≤ (f 4).val := L.frameBeforePrefix
  have hfit : (f 3).val+22 ≤ 2^g.w := by have := (f 4).isLt; omega
  have hA : (actualLength f v).val = raw.length := prepared_length L mt
  have hU : (actualLength f u).val = raw.length := prepared_length L m
  have hlen : actualLength f v = (raw.length : Word g.w) := Fin.ext (hA.trans (Fin.val_cast_of_lt
    (L.rawFits.trans_lt (f 1).isLt)).symm)
  have heq : actualLength f v = actualLength f u := Fin.ext (hA.trans hU.symm)
  have h := (finalImage c g lit raw values m L hlimit).frameData hfit
  refine ⟨h.2.1.trans ?_, h.2.2.1.trans ?_, h.2.2.2.trans ?_⟩
  · change copyFrame f v = LiveEvaluatorInitialize.copyPublic (copyBank c g) _
    funext i; fin_cases i <;> first | exact hlen | rfl
  · change skeletonFrame f v = skeletonFrame f u
    simp only [skeletonFrame,runtimeBase,heq]
  · change scatterFrame f v = scatterFrame f u
    simp only [scatterFrame,scatterBase,runtimeBase,heq]

/-- Starting in the tagged prepared memory, the prefix copier reads exactly
the evaluator prefix, the scatter sees the incoming exponent and order words,
and every cell of the previously initialized control bank is preserved. -/
theorem preparedInput (c : Constants) (g : Geometry) (lit : LiteralPrefix) (raw : List Bool)
    (values : Fin (c.labels.eval g) → Word (Nat.clog 2 (c.labels.eval g))) (m : Memory g.w)
    (L : PreparedLayout (lp c g) (fp c g) (op c g) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)))
    (hlimit : (Layout.shadow c).eval g < 2^g.w)
    (hspace : raw.length + (2*(c.labels.eval g*c.Z.eval g)+6*c.Z.eval g+4) ≤ c.radius.eval g+1)
    (perm : Fin (c.labels.eval g) ≃ Fin (c.labels.eval g)) (dense : Fin (c.labels.eval g) → Word (c.Z.eval g))
    (horder : ∀ i, (values i).val = (perm i).val)
    (incoming : ∀ q : Fin (c.labels.eval g*c.Z.eval g),
      m ((HeaderLayout.exponent c.lengths Layout.header .left).eval g+q.val) =
        PrimedInputRAM.encodeBit g.w (RAMSerialization.arrayBits _ _ dense q)) :
    let out := finalMemory c g lit raw values m
    (∀ j < raw.length, out (sourceAddress (copyBank c g) (j : Word g.w)).val = inputWord g.w raw (j/g.w)) ∧
    LiveEvaluatorReindex.Sources (scatterBank c g raw m) perm dense out ∧
    (∀ k : Fin (LiveEvaluatorEncoding.fieldWords (c.radius.eval g)), out (((copyBank c g) 1).val + k.val) =
      m (((copyBank c g) 1).val+k.val)) := by
  let cp := copyBank c g
  let sc := scatterBank c g raw m
  let t := c.labels.eval g
  let Z := c.Z.eval g
  let M := c.radius.eval g
  let f := fp c g
  have R := inputRegions c g raw m L hlimit hspace
  have image := finalImage c g lit raw values m L hlimit
  have hs : (tagAddr g lit).val < (f 0).val := tag_before_advice c g lit hlimit
  have hs' : (f 0).val ≤ (sc 0).val := R.incomingStart
  have hi : (sc 0).val + t*Z ≤ (cp 1).val := R.incomingEnd
  have hc : (cp 1).val + LiveEvaluatorEncoding.fieldWords M ≤ (f 3).val := R.configEnd
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · intro j hj
    obtain ⟨ha,hr⟩ := prefixSource c g raw j hj L
    rw [ha]
    exact image.rawWord _ hr
  · intro q
    change finalMemory c g lit raw values m ((sc 0).val+q.val) = _
    have hq : q.val < t*Z := q.isLt
    rw [beforeFrame_preserved c g lit raw values m L hlimit _ (by omega)
      (show (sc 0).val+q.val < (f 3).val by omega)]
    exact R.incoming ▸ incoming q
  · intro i
    exact (image.ordinalWord i).trans (horder i)
  · intro k
    have hk : k.val < LiveEvaluatorEncoding.fieldWords M := k.isLt
    exact beforeFrame_preserved c g lit raw values m L hlimit _
      (show (tagAddr g lit).val < (cp 1).val + k.val by omega)
      (show (cp 1).val+k.val < (f 3).val by omega)

end LiveProgram.Advice

end VPVNP
end Computability
end OAI

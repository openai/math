import OAI.Optimization.LinearProgramming.PrimalDual.PassesRAM
import OAI.Optimization.LinearProgramming.PrimalDual.Raw

/-! Physical RAM output decoder for the unbounded branch of Corollary 1.2. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape Matrix

/-- The first pass extracts signed equation multipliers into the staged ray
window. The next two passes compute their objective and divide by it in place.
Two final copies serialize the original feasible point followed by the ray. -/
def rayDecoder : Block :=
  .seq (OutputPass.scanFromRegs .difference 8 9 11 6)
    (.seq (OutputPass.scanFromRegs .dot 10 11 10 6)
      (.seq (OutputPass.scanFromRegs .normalize 11 11 11 6)
        (.seq (copyFromRegs false 13 12 6) (copyFromRegs true 14 15 7))))

/-- Inputs are placed before a fresh staging area containing both output vectors.
The last source and target addresses initialize the descending copy to address zero. -/
structure RayReady (d : Nat) (s : Memory ℚ) (pos neg obj base out : Nat) : Prop where
  n : s.index 6 = d
  total : s.index 7 = 2*d
  plus : s.index 8 = pos
  minus : s.index 9 = neg
  objective : s.index 10 = obj
  ray : s.index 11 = out+d
  staging : s.index 12 = out
  basePoint : s.index 13 = base
  srcLast : s.index 14 = out+2*d-1
  dstLast : s.index 15 = 2*d-1
  plusHigh : 4 ≤ pos
  minusHigh : 4 ≤ neg
  objHigh : 4 ≤ obj
  baseHigh : 4 ≤ base
  outHigh : 4 ≤ out
  plusBefore : pos+d ≤ out
  minusBefore : neg+d ≤ out
  objBefore : obj+d ≤ out
  baseBefore : base+d ≤ out
  disjoint : 2*d ≤ out

theorem rayDecoder_correct {m d H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c x₀ : Fin d → ℚ) (hx₀ : Feasible A b x₀) (joint : State ℚ)
    (hj : Certificate (finJointMatrix A b c) (finJointRhs b c) (readVector joint 0 (m+(m+(d+(d+1))))))
    (s : Memory ℚ) (pos neg obj base out : Nat) (abi : RayReady d s pos neg obj base out)
    (hs : Good (fun q => ratBits q ≤ H) s)
    (hp : Holds s pos (fun j : Fin d => joint.data (2*m+j.val)))
    (hn : Holds s neg (fun j : Fin d => joint.data (2*m+d+j.val)))
    (hc : Holds s obj c) (hx : Holds s base x₀) :
    ∃ t, Eval (Good (fun q => ratBits q ≤ decoderLimit d H)) rayDecoder s (51*d+29) t ∧
      OptimizationOutput A b c {t.atPC 0 with output := some 2} := by
  let a := fun j : Fin d => joint.data (2*m+j.val)
  let b' := fun j : Fin d => joint.data (2*m+d+j.val)
  let f := a-b'
  let den := c ⬝ᵥ f
  let F := out+d
  have certified := raw_joint_ray A b c x₀ hx₀ joint hj
  change den < 0 ∧ A *ᵥ (fun j => f j / den) ≤ 0 ∧ c ⬝ᵥ (fun j => f j / den) = 1 at certified
  obtain ⟨hden,ray,gain⟩ := certified
  obtain ⟨hH,h0,hDiff,_,hSum,_,hProd,hDiv⟩ := decoderLimit_bounds d H
  have safe : Good (fun q => ratBits q ≤ decoderLimit d H) s := fun i => (hs i).trans hH
  have ca (i : Fin d) : ratBits (a i) ≤ H := (congrArg ratBits (hp i)).symm.trans_le (hs _)
  have cb (i : Fin d) : ratBits (b' i) ≤ H := (congrArg ratBits (hn i)).symm.trans_le (hs _)
  have cc (i : Fin d) : ratBits (c i) ≤ H := (hc i) ▸ hs (obj+i.val)
  have cf (i : Fin d) : ratBits (f i) ≤ differenceWidth H :=
    (ratBits_sub_le (a i) (b' i)).trans (by unfold differenceWidth; linarith [ca i,cb i])
  have cg : ratBits den ≤ dotWidth d H (differenceWidth H) := by
    simpa only [partialDot_full] using partialDot_bits c f cc cf d le_rfl
  have hF : 4 ≤ F := by dsimp [F]; have := abi.outHigh; omega
  have sep₁ : pos+d ≤ F := abi.plusBefore.trans (Nat.le_add_right _ _)
  have sep₂ : neg+d ≤ F := abi.minusBefore.trans (Nat.le_add_right _ _)
  obtain ⟨s1,e1,wF,fr1,ix1⟩ := differencePass a b' pos neg F 8 9 11 6 s safe
    (by decide) (by decide) (by decide) (by decide) abi.plus abi.minus abi.ray abi.n
    abi.plusHigh abi.minusHigh hF (.inr (.inl sep₁)) (.inr (.inl sep₂)) hp hn ca cb hDiff h0
  have objBefore (i : Fin d) : obj+i.val < F := by dsimp [F]; have := abi.objBefore; omega
  have baseBefore (i : Fin d) : base+i.val < F := by dsimp [F]; have := abi.baseBefore; omega
  have wc1 : Holds s1 obj c := fun i =>
    (fr1 _ (by have := abi.objHigh; omega) (.inl (objBefore i))).trans (hc i)
  obtain ⟨s2,e2,acc,fr2,ix2⟩ := dotPass c f obj F 10 11 6 s1 e1.safe_end
    (by decide) (by decide) (by decide) ((ix1 _ (by decide)).trans abi.objective)
    ((ix1 _ (by decide)).trans abi.ray) ((ix1 _ (by decide)).trans abi.n)
    abi.objHigh hF wc1 wF cc cf hProd hSum h0
  have i2 (k : Nat) (hk : 6 ≤ k) : s2.index k = s.index k := (ix2 k hk).trans (ix1 k hk)
  have wf2 : Holds s2 F f := fun i => (fr2 _ (by omega)).trans (wF i)
  obtain ⟨s3,e3,wv,fr3,ix3⟩ := normalizeInPlace f den F 11 6 s2 e2.safe_end
    (by decide) (by decide) ((i2 _ (by decide)).trans abi.ray) ((i2 _ (by decide)).trans abi.n)
    hF wf2 acc hden.ne cf cg hDiv h0
  have i3 (k : Nat) (hk : 6 ≤ k) : s3.index k = s.index k := (ix3 k hk).trans (i2 k hk)
  have wx3 : Holds s3 base x₀ := by
    intro i
    have high : 4 ≤ base+i.val := by have := abi.baseHigh; omega
    exact (fr3 _ high (.inl (baseBefore i))).trans ((fr2 _ high).trans
      ((fr1 _ high (.inl (baseBefore i))).trans (hx i)))
  obtain ⟨s4,e4,copied,fr4,ix4⟩ := copyFromRegs_correct false d base out 13 12 6 s3 e3.safe_end
    (by decide) (by decide) (by decide) ((i3 _ (by decide)).trans abi.basePoint)
    ((i3 _ (by decide)).trans abi.staging) ((i3 _ (by decide)).trans abi.n)
    (.inl abi.baseBefore) (show 0 < out from lt_of_lt_of_le (by decide : 0 < 4) abi.outHigh)
  have i4 (k : Nat) (hk : 6 ≤ k) : s4.index k = s.index k := (ix4 k hk).trans (i3 k hk)
  have wx4 : Holds s4 out x₀ := fun i => (copied _ i.isLt).trans (wx3 i)
  have wv4 : Holds s4 F (fun j => f j / den) := fun i =>
    (fr4 (F+i.val) (by omega) (.inr (by dsimp [F]; omega))).trans (wv i)
  obtain ⟨t,e5,serialized,_,_⟩ := copyFromRegs_correct true (2*d) out 0 14 15 7 s4 e4.safe_end
    (by decide) (by decide) (by decide) ((i4 _ (by decide)).trans abi.srcLast)
    (by simpa [startPointer] using (i4 15 (by decide)).trans abi.dstLast)
    ((i4 _ (by decide)).trans abi.total) (.inr (by simpa using abi.disjoint))
    (show 0 < out from lt_of_lt_of_le (by decide : 0 < 4) abi.outHigh)
  have ex : readVector ({t.atPC 0 with output := some 2}) 0 d = x₀ := by
    funext i
    simpa [readVector,Memory.atPC] using (serialized i.val (by omega)).trans (wx4 i)
  have ev : readVector ({t.atPC 0 with output := some 2}) d d = fun j => f j / den := by
    funext i
    have he := serialized (d+i.val) (by omega)
    exact (show t.data (d+i.val) = s4.data (F+i.val) by
      simpa only [F,Nat.zero_add,Nat.add_assoc] using he).trans (wv4 i)
  refine ⟨t,?_,Or.inr (Or.inr ⟨rfl,?_⟩)⟩
  · have cost : 51*d+29 = (10*d+6)+((10*d+7)+((10*d+6)+((7*d+5)+(7*(2*d)+5)))) := by omega
    rw [cost]; exact e1.seq (e2.seq (e3.seq (e4.seq e5)))
  · rw [ex,ev]; exact ⟨hx₀,ray,gain⟩

end PrimalDual
end LinearProgramming
end Optimization
end OAI

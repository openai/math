import OAI.Optimization.LinearProgramming.PrimalDual.UnpackFirst
import OAI.Optimization.LinearProgramming.PrimalDual.JointFrame
import OAI.Optimization.LinearProgramming.PrimalDual.SavedPair

/-! Prepare the second isolated call from the actual result of the first one.
The subroutine receives the joint matrix, while its saved odd bank contains exactly
the objective and first feasible point. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Tape RAM.Block Polynomial

private def encoderBind : List CursorBind := [.reg 0 41,.reg 1 43,.reg 2 44,.reg 3 46]

private def invocationBind : List CursorBind :=
  [.reg 9 52,.reg 11 53,.reg 13 46,.reg 15 50,.reg 17 47,.reg 19 49,.reg 21 51]

def stageJoint : Block := .seq unpackFirst (.seq (CursorBind.script encoderBind)
  (.seq JointRAM.encode (CursorBind.script invocationBind)))

structure JointReady {m d : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c x₀ : Fin d → ℚ)
    (B : Nat) (s : Memory ℚ) : Prop where
  rows : s.index 9 = rowCount m d
  cols : s.index 11 = d+m
  inputBase : s.index 13 = jointBase m d
  inputSize : s.index 15 = jointLen m d
  savedBase : s.index 17 = origin m d+m*d+m
  savedSize : s.index 19 = 2*d
  limit : s.index 21 = cutoff m d B
  originalRows : s.index 41=m
  originalCols : s.index 43=d
  input : ∀ j < jointLen m d, s.data (jointBase m d+j) =
    ((lpInput (finJointMatrix A b c) (finJointRhs b c))[j]?).getD 0
  saved : ∀ j < 2*d, s.data ((origin m d+m*d+m)+j) = ((List.ofFn c ++ List.ofFn x₀)[j]?).getD 0
  dataTail : ∀ i, cutoff m d B ≤ i → s.data (2*i)=0
  indexTail : ∀ i, cutoff m d B ≤ i → s.index (2*i)=0

noncomputable def stageBudget : Polynomial Nat :=
  termBudget firstTerms + JointRAM.encoderPolynomial + 8*X^2 + 16*X + 24

theorem eval_mono (p : Polynomial Nat) {n N : Nat} (h : n ≤ N) : p.eval n ≤ p.eval N := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  exact Finset.sum_le_sum fun _ _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

theorem stageJoint_correct {m d B H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c x₀ : Fin d → ℚ) (s : Memory ℚ) (safe : Good (fun q => ratBits q ≤ H) s) (hz : 3 ≤ H)
    (hm : s.index 9=m) (hd : s.index 11=d) (hB : s.index 21=B)
    (saved : ∀ j < origLen m d, s.data (3+2*j) = optInputWord A b c j)
    (guest : ∀ j : Fin d, s.data (2*j.val) = x₀ j)
    (dt : ∀ i, B+2 ≤ i → s.data (2*i)=0) (it : ∀ i, B+2 ≤ i → s.index (2*i)=0) :
    ∃ t k, Eval (Good (fun q => ratBits q ≤ H)) stageJoint s k t ∧ k ≤ stageBudget.eval (m+d+B) ∧
      JointReady A b c x₀ B t := by
  obtain ⟨u,j,e1,hj,r,original,base,frame⟩ := unpackFirst_correct A b c x₀ s safe hm hd hB saved guest
  let l : JointRAM.Layout ℚ := ⟨m,d,A,b,c,origin m d,jointBase m d⟩
  let v := CursorBind.install encoderBind u
  have hinit := CursorBind.run encoderBind u e1.safe_end
  have vm : v.index 0 = m := by simp [v,encoderBind,CursorBind.install,CursorBind.apply,r.mreg]
  have vd : v.index 1 = d := by simp [v,encoderBind,CursorBind.install,CursorBind.apply,r.dreg]
  have vs : v.index 2 = l.src := by simp [v,l,encoderBind,CursorBind.install,CursorBind.apply,r.orig]
  have vo : v.index 3 = l.dst := by simp [v,l,encoderBind,CursorBind.install,CursorBind.apply,r.joint]
  have vhi (i : Nat) (hh : 40 ≤ i) : v.index i = u.index i := hinit.index_frame
    (show (CursorBind.script encoderBind).indexWritesBelow 40 = true by decide) hh
  have high := (origin_above m d).2.2.2
  obtain ⟨w,k,e2,hk,hw⟩ := JointRAM.encode_correct l v hinit.safe_end (show ratBits 0 ≤ H from hz)
    (show ratBits (-1) ≤ H from hz) (fun q hq => by simpa [ratBits_neg] using hq)
    (show 2 ≤ origin m d by omega) (show origin m d+origLen m d ≤ jointBase m d by unfold jointBase; omega)
    vm vd vs vo original
  have wregs := r.transfer (fun i hh =>
    (JointRAM.encode_preserves_high e2 (show 32 ≤ i by omega)).trans (vhi i hh))
  let t := CursorBind.install invocationBind w
  have e3 := CursorBind.run invocationBind w e2.safe_end
  have whole : Eval (Good (fun q => ratBits q ≤ H)) stageJoint s
      (j+(4+(k+7))) t := e1.seq (hinit.seq (e2.seq e3))
  have scalar : t.data=w.data := rfl
  have savedPair := savedPair_firstWindow A b c x₀ w (origin m d) hw.input (by
    intro i
    change w.data (origin m d+origLen m d+i.val) = x₀ i
    rw [hw.outside _ (by omega) (.inl (by change _ < jointBase m d; unfold jointBase; omega))]
    exact base i)
  refine ⟨t,_,whole,?_,?_⟩
  · have he : JointRAM.encoderPolynomial.eval (m+d) ≤ JointRAM.encoderPolynomial.eval (m+d+B) :=
      eval_mono _ (by omega)
    have hcost : 8*origLen m d+8*d ≤ 8*(m+d+B)^2+16*(m+d+B) := by
      unfold origLen; ring_nf; omega
    change k ≤ JointRAM.encoderPolynomial.eval (m+d) at hk
    simp [stageBudget]; omega
  constructor
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.rows]
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.cols]
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.joint]
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.jointLen]
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.saved]
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.savedLen,two_mul]
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.limit]
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.mreg]
  · simp [t,invocationBind,CursorBind.install,CursorBind.apply,wregs.dreg]
  · intro i hi; exact hw.output i hi
  · exact savedPair
  · intro i h
    have he : jointBase m d+jointLen m d ≤ 2*i := by unfold cutoff at h; omega
    rw [scalar,hw.outside _ (by unfold cutoff at h; omega) (.inr he)]
    change u.data (2*i)=0
    rw [frame _ (by omega)]
    exact dt i (by unfold cutoff at h; omega)
  · intro i h
    have hi := whole.index_frame (show stageJoint.indexWritesBelow 128 = true by decide)
      (show 128 ≤ 2*i by unfold cutoff at h; omega)
    exact hi.trans (it i (by unfold cutoff at h; omega))

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.PrimalDual.DecoderHeader
import OAI.Optimization.LinearProgramming.PrimalDual.DecoderExit
import OAI.Optimization.LinearProgramming.PrimalDual.OptimalDecoder
import OAI.Optimization.LinearProgramming.PrimalDual.RayDecoder

/-! The decoder entry points used immediately after the caller unpacks oracle buffers.
They require only the original short address headers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape Matrix

def compactInfeasible : Block := .seq (Header.write 6 Header.certTerms) infeasibleDecoder
def compactOptimum : Block := .seq (Header.write 6 Header.optimumTerms) optimumDecoder
def compactRay : Block := .seq (Header.write 6 Header.rayTerms) rayDecoder

theorem compactInfeasible_correct {m d H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) (s : Memory ℚ) (base : Nat) (hs : Good (fun q => ratBits q ≤ H) s)
    (h0 : s.index 0=m) (h1 : s.index 1=base) (large : m ≤ base) (pos : 0 < base)
    (first : State ℚ) (cert : Certificate A b (readVector first 0 m))
    (atSource : Holds s base (readVector first 0 m)) :
    ∃ t k, Eval (Good (fun q => ratBits q ≤ H)) compactInfeasible s k t ∧ k ≤ 50*(m+1) ∧
      OptimizationOutput A b c {t.atPC 0 with output := some 0} := by
  obtain ⟨w,j,init,hj,wd,r6,r7,r8⟩ := Header.cert_header m base s hs h0 h1
  have atW : Holds w base (readVector first 0 m) := fun i => (congrFun wd _).trans (atSource i)
  obtain ⟨t,run,hout⟩ := infeasibleDecoder_correct A b c w base init.safe_end large pos
    r6 r7 r8 _ atW cert
  exact ⟨t,_,init.seq run,by omega,hout⟩

theorem compactOptimum_correct {m d H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) (s : Memory ℚ) (z obj : Nat) (hs : Good (fun q => ratBits q ≤ H) s)
    (h0 : s.index 0=m) (h1 : s.index 1=d) (h2 : s.index 2=z) (h3 : s.index 3=obj)
    (hz : 4 ≤ z) (hobj : 4 ≤ obj) (sep : d+m+1 ≤ z) (joint : State ℚ)
    (hj : Feasible (finJointMatrix A b c) (finJointRhs b c) (readVector joint 0 (d+m)))
    (hx : Holds s z (readVector joint 0 d)) (hy : Holds s (z+d) (readVector joint d m))
    (hc : Holds s obj c) :
    ∃ t k, Eval (Good (fun q => ratBits q ≤ decoderLimit d H)) compactOptimum s k t ∧
      k ≤ 60*(m+d+1) ∧ OptimizationOutput A b c {t.atPC 0 with output := some 1} := by
  have safe : Good (fun q => ratBits q ≤ decoderLimit d H) s :=
    fun i => (hs i).trans (decoderLimit_bounds d H).1
  obtain ⟨w,j,init,hj',wd,r6,r7,r8,r9,r10,r11⟩ := Header.optimum_header m d z obj s safe h0 h1 h2 h3
  have small : Good (fun q => ratBits q ≤ H) w := fun i => (congrFun wd i) ▸ hs i
  have ready : OptimumReady (m:=m) (d:=d) w z obj := ⟨r6,r7,r8,r9,r10,r11,hz,hobj,sep⟩
  obtain ⟨t,run,hout⟩ := optimumDecoder_correct A b c w z obj ready small joint hj
    (fun i => (congrFun wd _).trans (hx i)) (fun i => (congrFun wd _).trans (hy i))
    (fun i => (congrFun wd _).trans (hc i))
  exact ⟨t,_,init.seq run,by omega,hout⟩

/-- Compact unbounded-input channels: dimension, positive and negative certificate
blocks, objective vector, saved feasible point, and the fresh output workspace. -/
theorem compactRay_correct {m d H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c x₀ : Fin d → ℚ) (hx₀ : Feasible A b x₀) (joint : State ℚ)
    (hj : Certificate (finJointMatrix A b c) (finJointRhs b c) (readVector joint 0 (m+(m+(d+(d+1))))))
    (s : Memory ℚ) (pos neg obj base out : Nat) (hs : Good (fun q => ratBits q ≤ H) s)
    (r0 : s.index 0=d) (r1 : s.index 1=pos) (r2 : s.index 2=neg) (r3 : s.index 3=obj)
    (r4 : s.index 4=base) (r5 : s.index 5=out)
    (ph : 4 ≤ pos) (nh : 4 ≤ neg) (ch : 4 ≤ obj) (xh : 4 ≤ base) (oh : 4 ≤ out)
    (ps : pos+d ≤ out) (ns : neg+d ≤ out) (cs : obj+d ≤ out) (xs : base+d ≤ out) (os : 2*d ≤ out)
    (hp : Holds s pos (fun j : Fin d => joint.data (2*m+j.val)))
    (hn : Holds s neg (fun j : Fin d => joint.data (2*m+d+j.val)))
    (hc : Holds s obj c) (hx : Holds s base x₀) :
    ∃ t k, Eval (Good (fun q => ratBits q ≤ decoderLimit d H)) compactRay s k t ∧
      k ≤ 140*(d+1) ∧ OptimizationOutput A b c {t.atPC 0 with output := some 2} := by
  have safe : Good (fun q => ratBits q ≤ decoderLimit d H) s :=
    fun i => (hs i).trans (decoderLimit_bounds d H).1
  obtain ⟨w,j,ini,hcost,wd,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15⟩ :=
    Header.ray_header d pos neg obj base out s safe r0 r1 r2 r3 r4 r5
  have ready : RayReady d w pos neg obj base out :=
    ⟨i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,ph,nh,ch,xh,oh,ps,ns,cs,xs,os⟩
  have small : Good (fun q => ratBits q ≤ H) w := fun i => (congrFun wd i) ▸ hs i
  obtain ⟨t,run,hout⟩ := rayDecoder_correct A b c x₀ hx₀ joint hj w pos neg obj base out ready small
    (fun i => (congrFun wd _).trans (hp i)) (fun i => (congrFun wd _).trans (hn i))
    (fun i => (congrFun wd _).trans (hc i)) (fun i => (congrFun wd _).trans (hx i))
  exact ⟨t,_,ini.seq run,by omega,hout⟩

/-- A single dimension-only polynomial covers each compact header, decoder, and final halt. -/
theorem compact_decoder_steps (m d : Nat) :
    50*(m+1)+1 ≤ polyBound 141 1 (m+d) ∧ 60*(m+d+1)+1 ≤ polyBound 141 1 (m+d) ∧
      140*(d+1)+1 ≤ polyBound 141 1 (m+d) := by
  simp only [polyBound, pow_one]; omega

end PrimalDual
end LinearProgramming
end Optimization
end OAI

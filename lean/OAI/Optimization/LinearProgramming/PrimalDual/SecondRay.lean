import OAI.Optimization.LinearProgramming.PrimalDual.GatherPlan
import OAI.Optimization.LinearProgramming.PrimalDual.UnpackFirst
import OAI.Optimization.LinearProgramming.PrimalDual.FirstCertificate
import OAI.Optimization.LinearProgramming.RAM.EvalWeaken

/-! Return from the actual second Farkas call. Four strided scalar copies extract
both certificate blocks, the objective, and the saved feasible point. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Tape RAM.Block Polynomial

private def rayMoves : List Move := [⟨2,51,44,43⟩,⟨2,52,45,43⟩,⟨2,42,46,43⟩,⟨2,53,47,43⟩]
private def rayLow : List CursorBind := [.reg 0 43,.reg 1 44,.reg 2 45,.reg 3 46,.reg 4 47,.reg 5 48]

private def rayPrelude : Block := .seq (returnHeader 41 43)
  (.seq (Move.pack rayMoves) (CursorBind.script rayLow))

def secondRay : Block := .seq rayPrelude compactRay

private theorem ray_layout {a : Nat → Nat} {m d : Nat} (r : ReturnRegs a m d) :
    (∀ v ∈ rayMoves, Move.room a (returnBase m d) v) ∧ rayMoves.Pairwise (Move.apart a) := by
  constructor
  · intro v hv
    simp [rayMoves] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · change 6≤51 ∧ 6≤44 ∧ 6≤43 ∧ 0<2 ∧ a 51+2*a 43≤returnBase m d ∧
        returnBase m d≤a 44 ∧ ∀ i<a 43, a 51+2*i≠1
      rw [r.plusSrc,r.dreg,r.buffer]
      exact ⟨by decide,by decide,by decide,by decide,by unfold returnBase; omega,le_rfl,by omega⟩
    · change 6≤52 ∧ 6≤45 ∧ 6≤43 ∧ 0<2 ∧ a 52+2*a 43≤returnBase m d ∧
        returnBase m d≤a 45 ∧ ∀ i<a 43, a 52+2*i≠1
      rw [r.minusSrc,r.dreg,r.minus]
      exact ⟨by decide,by decide,by decide,by decide,by unfold returnBase; omega,by omega,by omega⟩
    · change 6≤42 ∧ 6≤46 ∧ 6≤43 ∧ 0<2 ∧ a 42+2*a 43≤returnBase m d ∧
        returnBase m d≤a 46 ∧ ∀ i<a 43, a 42+2*i≠1
      rw [r.odd,r.dreg,r.rayObj]
      exact ⟨by decide,by decide,by decide,by decide,by unfold returnBase; omega,by omega,by omega⟩
    · change 6≤53 ∧ 6≤47 ∧ 6≤43 ∧ 0<2 ∧ a 53+2*a 43≤returnBase m d ∧
        returnBase m d≤a 47 ∧ ∀ i<a 43, a 53+2*i≠1
      rw [r.xsrc,r.dreg,r.xbuf]
      exact ⟨by decide,by decide,by decide,by decide,by unfold returnBase; omega,by omega,by omega⟩
  · simp [rayMoves,Move.apart,r.buffer,r.dreg,r.minus,r.rayObj,r.xbuf]
    omega

private theorem ray_cursors {m d : Nat} (v : Memory ℚ) (r : ReturnRegs v.index m d) :
    let w := CursorBind.install rayLow v
    let R := returnBase m d
    w.index 0=d ∧ w.index 1=R ∧ w.index 2=R+d ∧ w.index 3=R+d+d ∧
      w.index 4=R+d+d+d ∧ w.index 5=R+d+d+d+d := by
  dsimp only
  let w := CursorBind.install rayLow v
  let R := returnBase m d
  have h0 : w.index 0=d := by simp [w,rayLow,CursorBind.install,CursorBind.apply,r.dreg]
  have h1 : w.index 1=R := by simp [w,rayLow,CursorBind.install,CursorBind.apply,r.buffer,R]
  have h2 : w.index 2=R+d := by simp [w,rayLow,CursorBind.install,CursorBind.apply,r.minus,R]
  have h3 : w.index 3=R+d+d := by simp [w,rayLow,CursorBind.install,CursorBind.apply,r.rayObj,R]
  have h4 : w.index 4=R+d+d+d := by simp [w,rayLow,CursorBind.install,CursorBind.apply,r.xbuf,R]
  have h5 : w.index 5=R+d+d+d+d := by simp [w,rayLow,CursorBind.install,CursorBind.apply,r.outbuf,R]
  exact ⟨h0,h1,h2,h3,h4,h5⟩

private structure PackedRay {d : Nat} (m : Nat) (c x₀ : Fin d → ℚ) (joint : State ℚ) (w : Memory ℚ) : Prop where
  dim : w.index 0=d
  plus : w.index 1=returnBase m d
  minus : w.index 2=returnBase m d+d
  obj : w.index 3=returnBase m d+d+d
  point : w.index 4=returnBase m d+d+d+d
  out : w.index 5=returnBase m d+d+d+d+d
  plusWords : Holds w (returnBase m d) (fun i : Fin d => joint.data (2*m+i.val))
  minusWords : Holds w (returnBase m d+d) (fun i : Fin d => joint.data (2*m+d+i.val))
  objWords : Holds w (returnBase m d+d+d) c
  pointWords : Holds w (returnBase m d+d+d+d) x₀

private theorem rayPrelude_correct {m d H : Nat} (c x₀ : Fin d → ℚ) (joint : State ℚ)
    (s : Memory ℚ) (safe : Good (fun q => ratBits q ≤ H) s) (hm : s.index 41=m) (hd : s.index 43=d)
    (even : ∀ i, s.data (2*i)=joint.data i) (obj : ∀ i : Fin d, s.data (3+2*i.val)=c i)
    (point : ∀ i : Fin d, s.data (3+2*(d+i.val))=x₀ i) :
    ∃ w j, Eval (Good (fun q => ratBits q ≤ H)) rayPrelude s j w ∧
      j ≤ (termBudget returnTerms).eval (m+d)+40*(d+1) ∧ PackedRay m c x₀ joint w := by
  obtain ⟨u,j,e1,hj',ud,r⟩ := returnHeader_correct s safe 41 43 m d (by decide) (by decide) hm hd
  let R := returnBase m d
  have high : 4+2*d ≤ R := by dsimp [R,returnBase]; omega
  obtain ⟨room,apart⟩ := ray_layout r
  obtain ⟨v,e2,get,_,idx⟩ := Move.pack_correct rayMoves u.index R u e1.safe_end (fun _ _ => rfl)
    (by omega) room apart
  have r' := r.transfer (fun i hi => idx i (by omega))
  let w := CursorBind.install rayLow v
  have e3 := CursorBind.run rayLow v e2.safe_end
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := ray_cursors v r'
  have hp : Holds w R (fun i : Fin d => joint.data (2*m+i.val)) := by
    intro i
    have eq := get ⟨2,51,44,43⟩ (by simp [rayMoves]) i.val (by simp [r.dreg])
    change v.data (R+i.val) = _
    simpa [R,r.buffer,r.plusSrc,ud,show ∀ j, m+m+m+m+2*j=2*(2*m+j) by omega,even] using eq
  have hn : Holds w (R+d) (fun i : Fin d => joint.data (2*m+d+i.val)) := by
    intro i
    have eq := get ⟨2,52,45,43⟩ (by simp [rayMoves]) i.val (by simp [r.dreg])
    change v.data (R+d+i.val) = _
    simpa [R,r.minus,r.minusSrc,ud,show ∀ j, m+m+m+m+d+d+2*j=2*(2*m+d+j) by omega,even] using eq
  have hc : Holds w (R+d+d) c := by
    intro i
    have eq := get ⟨2,42,46,43⟩ (by simp [rayMoves]) i.val (by simp [r.dreg])
    change v.data (R+d+d+i.val) = _
    simpa [R,r.rayObj,r.odd,ud,obj] using eq
  have hx : Holds w (R+d+d+d) x₀ := by
    intro i
    have eq := get ⟨2,53,47,43⟩ (by simp [rayMoves]) i.val (by simp [r.dreg])
    change v.data (R+d+d+d+i.val) = _
    simpa [R,r.xbuf,r.xsrc,ud,show ∀ j, 3+d+d+2*j=3+2*(d+j) by omega,point] using eq
  refine ⟨w,_,e1.seq (e2.seq e3),?_,⟨h0,h1,h2,h3,h4,h5,hp,hn,hc,hx⟩⟩
  change j+((rayMoves.map (Move.ticks u.index)).sum+6) ≤ _
  simp [rayMoves,Move.ticks,r.dreg]
  omega

private theorem ray_space (m d : Nat) :
    let R := returnBase m d
    4≤R ∧ 4≤R+d ∧ 4≤R+d+d ∧ 4≤R+d+d+d ∧ 4≤R+d+d+d+d ∧
    R+d≤R+d+d+d+d ∧ R+d+d≤R+d+d+d+d ∧ R+d+d+d≤R+d+d+d+d ∧
    R+d+d+d+d≤R+d+d+d+d ∧ 2*d≤R+d+d+d+d := by
  dsimp [returnBase]; omega

theorem secondRay_correct {m d H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c x₀ : Fin d → ℚ) (hx₀ : Feasible A b x₀) (joint : State ℚ)
    (hj : Certificate (finJointMatrix A b c) (finJointRhs b c) (readVector joint 0 (rowCount m d)))
    (s : Memory ℚ) (safe : Good (fun q => ratBits q ≤ H) s) (hm : s.index 41=m) (hd : s.index 43=d)
    (even : ∀ i, s.data (2*i)=joint.data i)
    (obj : ∀ i : Fin d, s.data (3+2*i.val)=c i)
    (point : ∀ i : Fin d, s.data (3+2*(d+i.val))=x₀ i) :
    ∃ t k, Eval (Good (fun q => ratBits q ≤ decoderLimit d H)) secondRay s k t ∧
      k ≤ returnBudget.eval (m+d) ∧ OptimizationOutput A b c {t.atPC 0 with output := some 2} := by
  obtain ⟨w,j,pre,hj',r⟩ := rayPrelude_correct c x₀ joint s safe hm hd even obj point
  let R := returnBase m d
  obtain ⟨ph,nh,ch,xh,oh,ps,ns,cs,xs,os⟩ := ray_space m d
  obtain ⟨t,k,run,hk,hout⟩ := compactRay_correct A b c x₀ hx₀ joint hj w R (R+d) (R+d+d)
    (R+d+d+d) (R+d+d+d+d) pre.safe_end r.dim r.plus r.minus r.obj r.point r.out
    ph nh ch xh oh ps ns cs xs os r.plusWords r.minusWords r.objWords r.pointWords
  have lift (u : Memory ℚ) (hs : Good (fun q => ratBits q ≤ H) u) :
      Good (fun q => ratBits q ≤ decoderLimit d H) u := fun i => (hs i).trans (decoderLimit_bounds d H).1
  refine ⟨t,j+k,(pre.weaken lift).seq run,?_,hout⟩
  simp [returnBudget]
  omega

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI

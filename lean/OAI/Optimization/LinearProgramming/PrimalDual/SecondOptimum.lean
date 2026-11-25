import OAI.Optimization.LinearProgramming.PrimalDual.BridgeLayout
import OAI.Optimization.LinearProgramming.PrimalDual.GatherPlan
import OAI.Optimization.LinearProgramming.PrimalDual.CompactDecoder
import OAI.Optimization.LinearProgramming.RAM.EvalWeaken

/-! Decode a finite optimum directly from the isolated second feasibility return. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Block RAM.Tape

private def jointEven : Move := ⟨2,40,44,49⟩
private def costOdd : Move := ⟨2,42,50,43⟩
private def optimumMoves : List Move := [jointEven,costOdd]
private def optimumRegisters : List CursorBind := [.reg 0 41,.reg 1 43,.reg 2 44,.reg 3 50]

/-- The two strided gathers extract the returned primal/dual point and the saved
objective. The final decoder forms the exact objective value and emits the optimum. -/
def secondOptimum : Block := .seq (returnHeader 41 43)
  (.seq (Move.pack optimumMoves) (.seq (CursorBind.script optimumRegisters) compactOptimum))

theorem secondOptimum_correct {m d H : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) (joint : State ℚ)
    (feasible : Feasible (finJointMatrix A b c) (finJointRhs b c) (readVector joint 0 (d+m)))
    (s : Memory ℚ) (safe : Good (fun v => ratBits v ≤ H) s) (hm : s.index 41=m) (hd : s.index 43=d)
    (even : ∀ i < d+m, s.data (2*i)=joint.data i) (odd : ∀ i : Fin d, s.data (3+2*i.val)=c i) :
    ∃ t k, Eval (Good (fun v => ratBits v ≤ decoderLimit d H)) secondOptimum s k t ∧
      k ≤ (termBudget returnTerms).eval (m+d)+300*(m+d+1) ∧
      OptimizationOutput A b c {t.atPC 0 with output := some 1} := by
  obtain ⟨u,j,header,hj,data,r⟩ := returnHeader_correct s safe 41 43 m d (by decide) (by decide) hm hd
  let R := returnBase m d
  have available : 4+2*(d+m) ≤ R := by dsimp [R,returnBase]; omega
  have room (v : Move) (hv : v ∈ optimumMoves) : Move.room u.index R v := by
    simp only [optimumMoves,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl
    · change 6≤40 ∧ 6≤44 ∧ 6≤49 ∧ 0<2 ∧ u.index 40+2*u.index 49≤R ∧ R≤u.index 44 ∧
        ∀ i<u.index 49, u.index 40+2*i≠1
      rw [r.even,r.zlen,r.buffer]
      exact ⟨by decide,by decide,by decide,by decide,by omega,le_rfl,by omega⟩
    · change 6≤42 ∧ 6≤50 ∧ 6≤43 ∧ 0<2 ∧ u.index 42+2*u.index 43≤R ∧ R≤u.index 50 ∧
        ∀ i<u.index 43, u.index 42+2*i≠1
      rw [r.odd,r.dreg,r.optObj]
      refine ⟨by decide,by decide,by decide,by decide,by omega,?_,?_⟩
      · change R ≤ R+(d+m)+1; omega
      · omega
  have apart : optimumMoves.Pairwise (Move.apart u.index) := by
    refine List.pairwise_cons.mpr ⟨?_,by simp⟩
    intro v hv
    have hv' : v=costOdd := by simpa using hv
    subst v
    exact Or.inl (show u.index 44+u.index 49 ≤ u.index 50 by rw [r.buffer,r.zlen,r.optObj]; omega)
  obtain ⟨v,gather,words,_,indices⟩ := Move.pack_correct optimumMoves u.index R u header.safe_end
    (fun _ _ => rfl) (by omega) room apart
  have point (i : ℕ) (hi : i<d+m) : v.data (R+i)=joint.data i := by
    have h := words jointEven (by simp [optimumMoves]) i (show i<u.index 49 by rwa [r.zlen])
    change v.data (u.index 44+i)=u.data (u.index 40+2*i) at h
    rw [r.buffer,r.even,Nat.zero_add,data] at h
    exact h.trans (even i hi)
  have objective (i : Fin d) : v.data (R+(d+m)+1+i.val)=c i := by
    have h := words costOdd (by simp [optimumMoves]) i.val (show i.val<u.index 43 by rw [r.dreg]; exact i.isLt)
    change v.data (u.index 50+i.val)=u.data (u.index 42+2*i.val) at h
    rw [r.optObj,r.odd,data] at h
    exact h.trans (odd i)
  let w := CursorBind.install optimumRegisters v
  have init := CursorBind.run optimumRegisters v gather.safe_end
  have v41 := (indices 41 (by decide)).trans r.mreg
  have v43 := (indices 43 (by decide)).trans r.dreg
  have v44 := (indices 44 (by decide)).trans r.buffer
  have v50 := (indices 50 (by decide)).trans r.optObj
  have h0 : w.index 0=m := by simp [w,optimumRegisters,CursorBind.install,CursorBind.apply,v41]
  have h1 : w.index 1=d := by simp [w,optimumRegisters,CursorBind.install,CursorBind.apply,v43]
  have h2 : w.index 2=R := by simp [w,optimumRegisters,CursorBind.install,CursorBind.apply,v44,R]
  have h3 : w.index 3=R+(d+m)+1 := by simp [w,optimumRegisters,CursorBind.install,CursorBind.apply,v50,R]
  have x : Holds w R (readVector joint 0 d) := by
    intro i
    change v.data (R+i.val)=joint.data (0+i.val)
    rw [Nat.zero_add]
    exact point i.val (by have := i.isLt; omega)
  have y : Holds w (R+d) (readVector joint d m) := by
    intro i
    change v.data (R+d+i.val)=joint.data (d+i.val)
    rw [Nat.add_assoc]
    exact point _ (by have := i.isLt; omega)
  obtain ⟨t,k,dec,hk,out⟩ := compactOptimum_correct A b c w R (R+(d+m)+1) init.safe_end
    h0 h1 h2 h3 (by omega) (by omega) (by omega) joint feasible x y objective
  have widen {blk : Block} {s' t' : Memory ℚ} {k' : ℕ}
      (e : Eval (Good (fun v => ratBits v ≤ H)) blk s' k' t') :
      Eval (Good (fun v => ratBits v ≤ decoderLimit d H)) blk s' k' t' :=
    e.weaken (fun _ hs i => (hs i).trans (decoderLimit_bounds d H).1)
  refine ⟨t,_,(widen header).seq ((widen gather).seq ((widen init).seq dec)),?_,out⟩
  change j+((optimumMoves.map (Move.ticks u.index)).sum+(4+k)) ≤ _
  simp only [optimumMoves,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Move.ticks,
    jointEven,costOdd,r.zlen,r.dreg]
  omega

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI

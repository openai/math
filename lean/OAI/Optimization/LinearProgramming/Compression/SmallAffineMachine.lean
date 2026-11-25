import OAI.Optimization.LinearProgramming.Compression.AffineRAMInput

/-! A fixed scalar RAM checks all-small proxy affine forms by exact three-way comparison. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Tags are 0 for a negative value, 1 for zero, and 2 for a positive value. -/
def smallAffineTag (x : ℚ) : ℕ := if x < 0 then 0 else if 0 < x then 2 else 1

/-- Replace the evaluator's unique terminal instruction by a zero constant, up to two
comparisons and the corresponding return. The source accumulator is register zero. -/
def smallAffineProgram : Program :=
  affineEvalProgram.take 10 ++
    [.const 1 0, .branchLT 0 1 13 12, .branchLT 1 0 15 14, .halt 0, .halt 1, .halt 2]

private theorem source_live {p : Program} {s u : State ℚ} (h : step p s = some u) :
    s.output = none := by
  cases ho : s.output with
  | none => rfl
  | some => simp [step,ho] at h

private theorem still_running {s u : State ℚ} (h : step affineEvalProgram s = some u)
    (hu : u.output = none) : step smallAffineProgram s = some u := by
  have hs := source_live h
  have hlen : s.pc < affineEvalProgram.length := by
    by_contra! hbad
    simp [step,hs,List.getElem?_eq_none hbad] at h
  have hlt : s.pc < 11 := hlen
  have low : s.pc < 10 := by
    by_contra! hpc
    have atHalt : s.pc = 10 := by omega
    have hi : some {s with output := some 0} = some u := by
      simpa [step,hs,atHalt,affineEvalProgram,execInstr] using h
    rw [← Option.some.inj hi] at hu
    contradiction
  have hb : s.pc < (affineEvalProgram.take 10).length := low
  have hsame : smallAffineProgram[s.pc]? = affineEvalProgram[s.pc]? := by
    change (affineEvalProgram.take 10 ++ _)[s.pc]? = (affineEvalProgram.take 10 ++ [.halt 0])[s.pc]?
    rw [List.getElem?_append_left hb,List.getElem?_append_left hb]
  simpa only [step,hs,hsame] using h

private theorem last_live {s t : State ℚ}
    (h : step affineEvalProgram s = some t) (ht : t.output = some 0) :
    s.output = none ∧ s.pc=10 ∧ s.data=t.data := by
  have hs := source_live h
  cases hi : affineEvalProgram[s.pc]? with
  | none => simp [step,hs,hi] at h
  | some op =>
    have he : execInstr op s=some t := by simpa [step,hs,hi] using h
    have halts : op = .halt 0 ∧ t.data=s.data := by
      cases op <;> simp only [execInstr] at he
      all_goals try split at he
      all_goals first | contradiction | (cases he; simp_all [State.putData, State.putIndex])
    rw [halts.1] at hi
    have onlyHalt (j : ℕ) (hj : affineEvalProgram[j]? = some (.halt 0)) : j=10 := by
      have hlen : j < 11 := by
        by_contra! hbad
        rw [List.getElem?_eq_none (show affineEvalProgram.length ≤ j from hbad)] at hj
        contradiction
      interval_cases j <;> simp_all [affineEvalProgram]
    exact ⟨hs,onlyHalt _ hi,halts.2.symm⟩

/-- Every prefix step before the unique halt is shared byte-for-byte by the comparison
program, including all address jumps. -/
private theorem replace_halt {P : State ℚ → Prop} {s t : State ℚ} (k : ℕ)
    (he : Execution affineEvalProgram P s (k+1) t) (ht : t.output=some 0) :
    ∃ u, Execution smallAffineProgram P s k u ∧ u.output=none ∧ u.pc=10 ∧ u.data=t.data := by
  induction k generalizing s with
  | zero =>
    cases he with
    | next hs hstep hrest =>
      cases hrest with
      | done =>
        exact ⟨_, .done _ hs, last_live hstep ht⟩
  | succ k ih =>
    cases he with
    | @next _ v _ _ hs hstep hrest =>
      have hv : v.output=none := by cases hrest with | next _ hv _ => exact source_live hv
      obtain ⟨u,hu,ho,hpc,hd⟩ := ih hrest
      exact ⟨u,.next hs (still_running hstep hv) hu,ho,hpc,hd⟩

private theorem compare_at_ten {B : ℕ} (s : State ℚ) (hl : s.output=none) (hc : s.pc=10)
    (hb : scalarBound B s) (hzero : ratBits 0 ≤ B) :
    ∃ k ≤ 4, ∃ v, Execution smallAffineProgram (scalarBound B) s k v ∧
      v.output=some (smallAffineTag (s.data 0)) ∧ v.data 0=s.data 0 := by
  let z := s.putData 1 0
  have zs : scalarBound B z := by
    intro j
    by_cases hj : j=1
    · subst j; simpa [z,State.putData] using hzero
    · simpa [z,State.putData,Function.update_of_ne hj] using hb j
  have first : step smallAffineProgram s = some z := by
    simp [z,step,smallAffineProgram,affineEvalProgram,execInstr,hc,hl]
  by_cases hneg : s.data 0 < 0
  · let a := {z with pc := 13}
    let b := {a with output := some 0}
    have e₁ : step smallAffineProgram z=some a := by
      simp [z,a,step,smallAffineProgram,affineEvalProgram,execInstr,State.putData,hl,hc,hneg]
    have e₂ : step smallAffineProgram a=some b := by
      simp [a,b,z,step,smallAffineProgram,affineEvalProgram,execInstr,State.putData,hl]
    refine ⟨3,by decide,b,.next hb first (.next zs e₁ (.next zs e₂ (.done _ zs))),?_,?_⟩
    · simp [b, smallAffineTag,hneg]
    · simp [b,a,z,State.putData]
  · let a := {z with pc := 12}
    have e₁ : step smallAffineProgram z=some a := by
      simp [z,a,step,smallAffineProgram,affineEvalProgram,execInstr,State.putData,hl,hc,hneg]
    by_cases hpos : 0 < s.data 0
    · let b := {a with pc := 15}
      let v := {b with output := some 2}
      have e₂ : step smallAffineProgram a=some b := by
        simp [z,a,b,step,smallAffineProgram,affineEvalProgram,execInstr,State.putData,hl,hpos]
      have e₃ : step smallAffineProgram b=some v := by
        simp [z,a,b,v,step,smallAffineProgram,affineEvalProgram,execInstr,State.putData,hl]
      refine ⟨4,le_rfl,v,.next hb first (.next zs e₁ (.next zs e₂ (.next zs e₃ (.done _ zs)))),?_,?_⟩
      · simp [v,smallAffineTag,hneg,hpos]
      · simp [v,b,a,z,State.putData]
    · let b := {a with pc := 14}
      let v := {b with output := some 1}
      have e₂ : step smallAffineProgram a=some b := by
        simp [z,a,b,step,smallAffineProgram,affineEvalProgram,execInstr,State.putData,hl,hpos]
      have e₃ : step smallAffineProgram b=some v := by
        simp [z,a,b,v,step,smallAffineProgram,affineEvalProgram,execInstr,State.putData,hl]
      refine ⟨4,le_rfl,v,.next hb first (.next zs e₁ (.next zs e₂ (.next zs e₃ (.done _ zs)))),?_,?_⟩
      · simp [v,smallAffineTag,hneg,hpos]
      · simp [v,b,a,z,State.putData]

/-- The machine reads the actual coefficient/argument pairs, evaluates the affine form,
and returns its exact sign and value. All scalar register sizes obey the evaluator's bound. -/
theorem smallAffineProgram_trace {n B : ℕ} (a x : Fin n → ℚ) (e : ℚ)
    (ha : ∀ i, (a i).num.natAbs ≤ B ∧ (a i).den ≤ B)
    (hx : ∀ i, (x i).num.natAbs ≤ B ∧ (x i).den ≤ B)
    (he : e.num.natAbs ≤ B ∧ e.den ≤ B) :
    ∃ k ≤ 9*n+6, ∃ t : Fin (k+1) → State ℚ,
      Trace smallAffineProgram (start [n] (e :: 0 :: 0 :: affineInputPairs a x)) k t ∧
      (t (Fin.last k)).output = some (smallAffineTag (e+dotProduct a x)) ∧
      (t (Fin.last k)).data 0 = e+dotProduct a x ∧ ∀ i, scalarBound (affineEvalBits n B) (t i) := by
  obtain ⟨v,hv,ho,hd,hs⟩ := affineVector_eval_trace a x e ha hx he
  obtain ⟨u,hu,ul,uc,ud⟩ := replace_halt (9*n+2) (Execution.of_trace hv hs) ho
  have uz : ratBits 0 ≤ affineEvalBits n B := by change 3 ≤ _; unfold affineEvalBits; omega
  obtain ⟨j,hj,z,hz,zt,zv⟩ := compare_at_ten u ul uc hu.safe_end uz
  obtain ⟨t,ht,hl,hb⟩ := (hu.append hz).to_trace
  have u0 : u.data 0 = e+dotProduct a x := (congrFun ud 0).trans hd
  exact ⟨_,by omega,t,ht,by rw [hl,zt,u0],by rw [hl,zv,u0],hb⟩

end Compression
end LinearProgramming
end Optimization
end OAI

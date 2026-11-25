import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixSemantics

/-! Composition of every adaptive query, signed rounding pass, and persistent pivot row. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotPrefixRAM

open RAM RAM.Block Contract OracleSegments

private theorem control_eval (m : Memory ℚ) (src H : ℕ) (hm : RowRAM.Within H m) :
    Eval (RowRAM.Within H) (.op (.addrCopy 14 src)) m 1 (controlMemory m src) :=
  Eval.op_addrCopy _ _ _ hm hm

private theorem branch_eval (m : Memory ℚ) (H : ℕ) (hm : RowRAM.Within H m) :
    Eval (RowRAM.Within H) (.op (.addrConst 15 1)) m 1 (branchMemory m) :=
  Eval.op_addrConst _ _ _ hm hm

private theorem within_mono {m : Memory ℚ} {a b : ℕ} (h : a ≤ b) (hm : RowRAM.Within a m) : RowRAM.Within b m :=
  fun i => (hm i).trans h

private theorem next_det {r a n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (ha : a < r) (rows : Fin a → PivotRow n)
    (row : PivotRow n) (price : Fin n → ℚ) (f : PivotKey n → ℚ)
    (hs : PivotStepSpec (D.submatrix (Fin.castLE ha) id) (fun j => (rows j).pivot) price f row) :
    (D.submatrix (Fin.castLE ha) (fun j => (Fin.lastCases (motive := fun _ => PivotRow n) row rows j).pivot)).det ≠ 0 := by
  have col : (fun j => (Fin.lastCases (motive := fun _ => PivotRow n) row rows j).pivot) = Fin.lastCases row.pivot (fun j => (rows j).pivot) := by
    funext j; refine Fin.lastCases ?_ (fun q => ?_) j <;> simp
  rw [col]
  have h := hs.nonzero
  rw [hs.minors] at h
  exact h

/-- Carry the fixed prefix algorithm through a trace semantics that proves each ordinary
batch execution and composes the surrounding scalar-free control instructions. -/
theorem run_with {tr : PrefixTrace} (rules : TraceRules tr) {r n B L extra C H : ℕ} (batch : Segment) (o : ScalarOracle ℚ) (packet : PivotKey n → List ℚ)
    (D : Matrix (Fin r) (Fin n) ℚ) (price : Fin n → ℚ) (base : Memory ℚ) (hist₀ : Contract.History ℚ)
    (Aux : Memory ℚ → Contract.History ℚ → Prop)
    (layout : Layout base r n B) (hD : LinearIndependent ℚ D.row) (hb : RowRAM.Within H base)
    (auxStable : FrameStable base r n Aux) (aux₀ : Aux base hist₀)
    (batchOK : BatchSound batch o packet base D price B L extra C Aux)
    (annotation : BatchAnnotation tr batch o base D price B extra Aux) :
    ∃ t final k, k ≤ r*stepCost n B C+6 ∧
      tr (program batch) (RowRAM.Within (H+r*stepWidth n L B extra)) base hist₀ k t final ∧
      Aux t final ∧ Outcome packet base D price B hist₀ t final := by
  let width (a : ℕ) := H+a*stepWidth n L B extra
  have grow {i j : ℕ} (h : i ≤ j) : width i ≤ width j := Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
  have next (a : ℕ) : PivotStageRAM.stageWidth n (width a+extra) L B = width (a+1) := by
    simp only [PivotStageRAM.stageWidth,width,stepWidth,Nat.succ_mul,Nat.add_assoc]
  have sufficient {a : ℕ} (ha : a < r) : width a+extra ≤ width r := by
    apply le_trans ?_ (grow ha)
    rw [← next]
    exact Nat.le_add_right _ _
  have loopRuns : ∀ d a (add : a+d = r) (rows : Fin a → PivotRow n) (seen : List (PivotKey n × ℚ))
      (m : Memory ℚ) (hist : Contract.History ℚ), Stored base m rows price B →
      (D.submatrix (Fin.castLE (show a ≤ r by omega)) (fun j => (rows j).pivot)).det ≠ 0 →
      MinorQuery.Run (pivotPrefix D price a (by omega)) seen (.inr (some rows)) →
      hist = answeredHistory packet seen hist₀ → m.index 14 = a → m.index 139 = 0 →
      Aux m hist → RowRAM.Within (width a) m →
      ∃ t final k, k ≤ d*stepCost n B C+1 ∧ tr (prefixLoop batch) (RowRAM.Within (width r)) m hist k t final ∧
        Aux t final ∧ Outcome packet base D price B hist₀ t final := by
    intro d
    induction d with
    | zero =>
      intro a add rows seen m hist stored _ req hh cursor status aux safe
      simp only [Nat.add_zero] at add
      subst a
      have rank := (stored.permanent 129 (by decide) (by decide) (by decide) (by decide) (by decide)).trans layout.rank
      have done := rules.loopFalse (.addrLT 14 129) (iteration batch) safe (by simp [Cond.test,cursor,rank]) (h := hist)
      exact ⟨m,hist,1,by simp,done,aux,.completed seen rows req hh status stored⟩
    | succ d ih =>
      intro a add rows seen m hist stored old req hh cursor _ aux safe
      have more : a < r := by omega
      have rank := (stored.permanent 129 (by decide) (by decide) (by decide) (by decide) (by decide)).trans layout.rank
      have loopGuard : (Cond.addrLT 14 129).test m = true := by simp [Cond.test,cursor,rank,more]
      obtain ⟨b,hb',kb,hkb,rawBatch,auxB,storeB,result⟩ := batchOK a more rows m hist (width a) stored old aux safe
      have safeB : RowRAM.Within (width a+extra) b := Runs.finish rawBatch
      have wideB : RowRAM.Within (width r) b := within_mono (sufficient more) safeB
      have annotated := annotation a more rows m hist (width a) stored old aux safe b hb' kb rawBatch
      have first := rules.weaken annotated (fun _ h => within_mono (sufficient more) h)
      have chooseBranch := rules.core (branch_eval b (width r) wideB) hb'
      have stateB := storeB.branch layout.pivotsHigh
      have auxBranch := auxStable b (branchMemory b) hb' (CallerFrame.branch base b r n) auxB
      rcases result with ⟨xs,f,row,good,actual,ev,packed,answers⟩ | ⟨xs,key,bad,actual,answers⟩
      · have guard : (Cond.addrLT 139 15).test (branchMemory b) = true := by simp [Cond.test,branchMemory,good]
        let A := D.submatrix (Fin.castLE more) id
        let J := fun j => (rows j).pivot
        have independent : LinearIndependent ℚ A.row := hD.comp (Fin.castLE more) (Fin.castLE_injective more)
        have minor : (A.submatrix Fin.castSucc J).det ≠ 0 := old
        obtain ⟨row',ev',spec⟩ := pivotStep_eval A J price f independent minor
        have same : row' = row := Option.some.inj (ev'.symm.trans ev)
        subst row'
        obtain ⟨v,kv,hkv,compute,storeV,frameV,statusV⟩ := acceptRow A rows row price f base (branchMemory b)
          layout more stateB packed.branch safeB ev spec
        rw [next] at compute
        have safeV := compute.safe_end
        have wideV := within_mono (grow more) safeV
        have num := rules.weaken (rules.core compute hb') (fun _ h => within_mono (grow more) h)
        have move := rules.core (control_eval v 128 (width r) wideV) hb'
        have stage : tr success (RowRAM.Within (width r)) (branchMemory b) hb' (kv+1) (controlMemory v 128) hb' := rules.seq num move
        have pass := rules.seq first (rules.seq chooseBranch (rules.branchTrue (b := .core (.op (.addrCopy 14 129))) guard stage))
        have auxV := auxStable _ _ hb' frameV auxBranch
        have auxNext := auxStable _ _ hb' (CallerFrame.control base v r n 128) auxV
        have reqNext := prefixRun_succ (ha := more) req actual
        have histNext : hb' = answeredHistory packet (seen++xs) hist₀ := by rw [answers,hh,answeredHistory_append]
        have status : (controlMemory v 128).index 139 = 0 := statusV.trans good
        have nextCursor : (controlMemory v 128).index 14 = a+1 := by simp [controlMemory,storeV.length]
        obtain ⟨t,h,k,hk,tail,auxT,done⟩ := ih (a+1) (by omega) (Fin.lastCases row rows) (seen++xs) (controlMemory v 128) hb'
          (storeV.control layout.pivotsHigh 128) (next_det D more rows row price f spec) reqNext histNext nextCursor status auxNext safeV
        have all := rules.loopTrue loopGuard pass tail
        refine ⟨t,h,_,?_,all,auxT,done⟩
        rw [Nat.succ_mul]
        dsimp [stepCost] at *
        omega
      · have guard : (Cond.addrLT 139 15).test (branchMemory b) = false := by simp [Cond.test,branchMemory,bad]
        let endMem := controlMemory (branchMemory b) 129
        have stop := rules.core (control_eval (branchMemory b) 129 (width r) wideB) hb'
        have pass := rules.seq first (rules.seq chooseBranch (rules.branchFalse (a := success) guard stop))
        have endGuard : (Cond.addrLT 14 129).test endMem = false := by simp [endMem,controlMemory,Cond.test]
        have tail := rules.loopFalse (.addrLT 14 129) (iteration batch) (m := endMem) (P := RowRAM.Within (width r)) (h := hb') (fun i => wideB i) endGuard
        have all := rules.loopTrue loopGuard pass tail
        have full := prefixRun_restart_extend (b := r) more le_rfl (prefixRun_succ_restart (ha := more) req actual)
        have resultHistory : hb' = (packet key,[1]) :: answeredHistory packet (seen++xs) hist₀ := by rw [answers,hh,answeredHistory_append]
        have auxT := auxStable _ _ hb' (CallerFrame.control base (branchMemory b) r n 129) auxBranch
        refine ⟨endMem,hb',_,?_,all,auxT,.restarted (seen++xs) key a more rows full resultHistory bad (stateB.control layout.pivotsHigh 129)⟩
        rw [Nat.succ_mul]; dsimp [stepCost]; omega
  let s := initial base
  let u := controlMemory s 128
  have hs := Stored.empty base price B
  have hsAux := auxStable _ _ hist₀ (CallerFrame.initial base r n) aux₀
  have huAux := auxStable _ _ hist₀ (CallerFrame.control base s r n 128) hsAux
  have startSteps := initialize_eval base (fun q => ratBits q ≤ width r) (within_mono (Nat.le_add_right H _) hb)
  have initRun := rules.core startSteps hist₀
  have initMove := rules.core (control_eval s 128 (width r) startSteps.safe_end) hist₀
  have baseReq : MinorQuery.Run (pivotPrefix D price 0 (Nat.zero_le _)) [] (.inr (some Fin.elim0)) := .done _
  obtain ⟨t,final,k,hk,tail,auxT,out⟩ := loopRuns r 0 (by simp) Fin.elim0 [] u hist₀ (hs.control layout.pivotsHigh 128)
    (by simp) baseReq (by simp [answeredHistory]) (by simp [u,s,controlMemory,initial]) (by simp [u,s,controlMemory,initial])
    huAux (by intro i; change ratBits (base.data i) ≤ width 0; simpa [width] using hb i)
  exact ⟨t,final,_,by omega,rules.seq initRun (rules.seq initMove tail),auxT,out⟩

/-- The actual oracle program traverses all rows unless a real scalar answer requests
restart. Its instruction bound is dimension-polynomial whenever the named-minor batch
bound is, and its register bound accumulates the independent local increments additively. -/
theorem run {r n B L extra C H : ℕ} (batch : Segment) (o : ScalarOracle ℚ) (packet : PivotKey n → List ℚ)
    (D : Matrix (Fin r) (Fin n) ℚ) (price : Fin n → ℚ) (base : Memory ℚ) (hist₀ : Contract.History ℚ)
    (Aux : Memory ℚ → Contract.History ℚ → Prop)
    (layout : Layout base r n B) (hD : LinearIndependent ℚ D.row) (hb : RowRAM.Within H base)
    (auxStable : FrameStable base r n Aux) (aux₀ : Aux base hist₀)
    (batchOK : BatchSound batch o packet base D price B L extra C Aux) :
    ∃ t final k, k ≤ r*stepCost n B C+6 ∧
      Runs (program batch) o (RowRAM.Within (H+r*stepWidth n L B extra)) base hist₀ k t final ∧
      Aux t final ∧ Outcome packet base D price B hist₀ t final := by
  apply run_with (ordinaryRules o) batch o packet D price base hist₀ Aux layout hD hb auxStable aux₀ batchOK
  unfold BatchAnnotation
  intros
  assumption

/-- Projection to the genuine `Contract.OracleRun` relation, with a terminal halt and
full scalar history. `run` also exposes the guard at every step for further composition. -/
theorem halted {r n B L extra C H : ℕ} (batch : Segment) (o : ScalarOracle ℚ) (packet : PivotKey n → List ℚ)
    (D : Matrix (Fin r) (Fin n) ℚ) (price : Fin n → ℚ) (base : Memory ℚ) (hist₀ : Contract.History ℚ)
    (Aux : Memory ℚ → Contract.History ℚ → Prop)
    (layout : Layout base r n B) (hD : LinearIndependent ℚ D.row) (hb : RowRAM.Within H base)
    (stable : FrameStable base r n Aux) (aux : Aux base hist₀)
    (ok : BatchSound batch o packet base D price B L extra C Aux) :
    ∃ t final k, k ≤ r*stepCost n B C+7 ∧
      OracleRun ((program batch).emit 0 ++ [.core (.halt 0)]) o ⟨base.atPC 0,hist₀⟩ k
        ⟨{ t.atPC (program batch).size with output := some 0 },final⟩ ∧ Aux t final ∧ Outcome packet base D price B hist₀ t final := by
  obtain ⟨t,final,k,hk,run',auxT,out⟩ := run batch o packet D price base hist₀ Aux layout hD hb stable aux ok
  exact ⟨t,final,k+1,by omega,(Runs.halted run' 0).plain,auxT,out⟩

end PivotPrefixRAM
end Geometry
end LinearProgramming
end Optimization
end OAI

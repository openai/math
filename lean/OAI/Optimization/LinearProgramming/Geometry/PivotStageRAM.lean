import OAI.Optimization.LinearProgramming.Geometry.PivotPrepareRAM
import OAI.Optimization.LinearProgramming.Geometry.PivotCorrespondence
import OAI.Optimization.LinearProgramming.Geometry.RoundedPass

/-! One RAM program selects the pivot and writes the rounded row from packed replies. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotStageRAM

open RAM RAM.Block

/-- The rounding kernel reuses low address registers. Save the winning column in address
13 so it remains available for the next pivot stage. -/
def block : Block :=
  .seq PivotRAM.scanBlock <| .seq PivotPrepareRAM.block <|
    .seq (.op (.addrCopy 13 3)) (RowRAM.pass PowerRAM.signedBlock)

def scoreWidth (H : ℕ) : ℕ := 3 + 4*H

/-- A stage adds a polynomial in the dimensions and the packed source widths. This
bound is independent of the widths of unrelated scratch values in the input RAM. -/
def widthIncrement (n L B : ℕ) : ℕ := scoreWidth L + n * PowerRAM.signedWidth 0 (scoreWidth L) B

def stageWidth (n H L B : ℕ) : ℕ := H + widthIncrement n L B

/-- Observable effects on the designated row, the chosen column, and the caller's frame. -/
structure Staged {n : ℕ} (row : PivotRow n) (price : Fin n → ℚ) (m t : Memory ℚ) (B : ℕ) : Prop where
  pivot : t.index 13 = row.pivot.val
  rounded (j : Fin n) : t.data (m.index 8+j.val) = row.rounded price B j
  data (i) : 27 ≤ i → (i < m.index 8 ∨ m.index 8+n ≤ i) → t.data i = m.data i
  index (i) : 6 ≤ i → i ≠ 7 → i ≠ 9 → i ≠ 10 → i ≠ 11 → i ≠ 12 → i ≠ 13 → t.index i = m.index i

/-- The triples contain signed minors, the answered compressed logs, and the prices. All
requests precede this deterministic block. Both the winner and every rounded coordinate
agree with the answered adaptive pivot step, even on ties or zero minors. -/
theorem block_spec {n k : ℕ} (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (price : Fin n → ℚ) (f : PivotKey n → ℚ) (row : PivotRow n)
    (hrun : MinorQuery.eval f (pivotStep D J price) = some row)
    (hrow : PivotStepSpec D J price f row) (m : Memory ℚ) (H L B : ℕ)
    (hm : RowRAM.Within H m)
    (hlocal : ∀ j : Fin n, ∀ q < 3, ratBits (m.data (m.index 4+3*j.val+q)) ≤ L) (hB : m.index 6 = B) (hn : m.index 0 = n)
    (hi : 27 ≤ m.index 4) (ho : 27 ≤ m.index 8)
    (hsep : m.index 4+3*n ≤ m.index 8 ∨ m.index 8+n ≤ m.index 4)
    (hraw : ∀ j : Fin n, PivotRAM.inputMinor m j.val = row.raw j)
    (hlog : ∀ j : Fin n, PivotRAM.inputLog m j.val = row.logs j)
    (hprice : ∀ j : Fin n, PivotRAM.inputPrice m j.val = price j) :
    ∃ t c, c ≤ n*(32*B+206)+17 ∧ Eval (RowRAM.Within (stageWidth n H L B)) block m c t ∧
      Staged row price m t B := by
  have hscore (j : Fin n) : PivotRAM.inputScore m j.val = row.logs j-price j := by
    rw [PivotRAM.inputScore,hlog,hprice]
  have hw := PivotRAM.incumbent_eq_pivotStep D J price f row hrun m hraw hscore
  let W := H+scoreWidth L
  have lh : L ≤ scoreWidth L := by dsimp [scoreWidth]; omega
  have ll : scoreWidth L ≤ W := Nat.le_add_left _ _
  have hscan : RowRAM.Within W m := fun j => (hm j).trans (Nat.le_add_right _ _)
  have hold : ratBits 0 ≤ W := by rw [show ratBits 0 = 3 by decide]; dsimp [W,scoreWidth]; omega
  have hsub (i : ℕ) (hi : i < n) : ratBits (PivotRAM.inputScore m i) ≤ scoreWidth L := by
    have hd := PrimalDual.ratBits_sub_le (PivotRAM.inputLog m i) (PivotRAM.inputPrice m i)
    have hl : ratBits (PivotRAM.inputLog m i) ≤ L := hlocal ⟨i,hi⟩ 1 (by decide)
    have hp : ratBits (PivotRAM.inputPrice m i) ≤ L := hlocal ⟨i,hi⟩ 2 (by decide)
    unfold scoreWidth PivotRAM.inputScore
    omega
  obtain ⟨u,c,hc,scan,win,best,udata,uidx,u0⟩ := PivotRAM.scanBlock_spec_full m
    (fun q => ratBits q ≤ W) hscan hold (by omega) (fun i hj => (hsub i (hn ▸ hj)).trans ll)
  have u3 : u.index 3 = row.pivot.val := by simpa only [hn,hw,Option.getD_some] using win
  have u5 : u.data 5 = row.logs row.pivot-price row.pivot :=
    (best _ (by rw [hn, hw])).trans (hscore _)
  obtain ⟨v,prep,hv⟩ := PivotPrepareRAM.block_spec u (fun q => ratBits q ≤ W) scan.safe_end
  let w := v.putIndex 13 row.pivot.val
  have v3 : v.index 3 = row.pivot.val := (hv.index _ (by decide) (by decide) (by decide) (by decide)).trans u3
  have save : Eval (RowRAM.Within W) (.op (.addrCopy 13 3)) v 1 w := by
    simpa only [w,v3] using Eval.op_addrCopy v 13 3 prep.safe_end prep.safe_end
  have w7 : w.index 7 = m.index 4 := (hv.source).trans (uidx 4 (by decide))
  have w9 : w.index 9 = n := (hv.count.trans u0).trans hn
  have w6 : w.index 6 = B := (hv.index _ (by decide) (by decide) (by decide) (by decide)).trans ((uidx 6 (by decide)).trans hB)
  have w8 : w.index 8 = m.index 8 := (hv.index _ (by decide) (by decide) (by decide) (by decide)).trans (uidx 8 (by decide))
  have w21 : w.data 21 = row.raw row.pivot := by
    change v.data 21 = _
    rw [hv.pivot, uidx 4 (by decide),u3,udata _ (by omega)]
    exact hraw _
  have w22 : w.data 22 = row.logs row.pivot-price row.pivot := hv.winning.trans u5
  have wData (i : ℕ) (h : 27 ≤ i) : w.data i = m.data i := (hv.data _ (by omega) (by omega)).trans (udata _ (by omega))
  have hwLocal : RowRAM.PackedWidth w (scoreWidth L) := by
    constructor
    · rw [w21,← hraw row.pivot]
      exact (hlocal row.pivot 0 (by decide)).trans lh
    · rw [w22,← hscore row.pivot]
      exact hsub _ row.pivot.isLt
    · intro j hj q hq
      rw [w7,wData _ (by omega)]
      exact (hlocal ⟨j,w9 ▸ hj⟩ q hq).trans lh
  obtain ⟨t,l,hl,rounded,out,hf,ia⟩ := RowRAM.signed_pass_matches_localWidth row price w W (scoreWidth L) B
    save.safe_end hwLocal w6 w9 w21 w22 hrow.nonzero hrow.maximizing
    (fun j => by rw [w7,wData _ (by omega)]; exact hraw j)
    (fun j => by rw [w7,wData _ (by omega)]; exact hlog j)
    (fun j => by rw [w7,wData _ (by omega)]; exact hprice j)
    (w7 ▸ hi) (w8 ▸ ho) (by simpa only [w7,w8] using hsep)
  have hW : stageWidth n H L B = W+n*PowerRAM.signedWidth 0 (scoreWidth L) B := by
    simp only [stageWidth,widthIncrement,W,Nat.add_assoc]
  have wider (s : Memory ℚ) (safe : RowRAM.Within W s) : RowRAM.Within (stageWidth n H L B) s :=
    fun i => (safe i).trans (by rw [hW]; exact Nat.le_add_right _ _)
  rw [← hW] at rounded
  refine ⟨t, c+(6*u.index 3+7+(1+l)), ?_, (PowerRAM.weaken scan wider).seq
    ((PowerRAM.weaken prep wider).seq ((PowerRAM.weaken save wider).seq rounded)), ?_⟩
  · rw [u3]
    rw [hn] at hc
    have hp := row.pivot.isLt
    rw [show n*(32*B+206)+17 = (19*n+5)+(6*n+7)+(1+(n*(32*B+181)+4)) by ring]
    omega
  · refine ⟨?_,?_,?_,?_⟩
    · simpa [w] using ia 13 (by decide) (by decide) (by decide) (by decide)
    · intro j; simpa only [w8] using out j
    · intro i h outside
      exact (hf i h (by simpa only [w8] using outside)).trans (wData i h)
    · intro i hi6 h7 h9 h10 h11 h12 h13
      have hwi : w.index i = m.index i := by
        rw [show w.index i = v.index i by simp [w,h13],hv.index _ h7 h9 h10 h11,uidx _ (by omega)]
      exact (ia _ hi6 h10 h11 h12).trans hwi

/-- Full trace of the compiled finite program, including its halt. The mathematical
assumptions are the row independence and previous nonzero minor of a valid pivot stage. -/
theorem trace_matches {n k : ℕ} (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (price : Fin n → ℚ) (f : PivotKey n → ℚ) (row : PivotRow n)
    (hrun : MinorQuery.eval f (pivotStep D J price) = some row)
    (hD : LinearIndependent ℚ D.row) (hJ : (D.submatrix Fin.castSucc J).det ≠ 0)
    (m : Memory ℚ) (H L B : ℕ) (hm : RowRAM.Within H m)
    (hlocal : ∀ j : Fin n, ∀ q < 3, ratBits (m.data (m.index 4+3*j.val+q)) ≤ L)
    (hB : m.index 6 = B) (hn : m.index 0 = n) (hi : 27 ≤ m.index 4) (ho : 27 ≤ m.index 8)
    (hsep : m.index 4+3*n ≤ m.index 8 ∨ m.index 8+n ≤ m.index 4)
    (hraw : ∀ j : Fin n, PivotRAM.inputMinor m j.val = row.raw j)
    (hlog : ∀ j : Fin n, PivotRAM.inputLog m j.val = row.logs j)
    (hprice : ∀ j : Fin n, PivotRAM.inputPrice m j.val = price j) :
    ∃ c ≤ n*(32*B+206)+18, ∃ run : Fin (c+1) → State ℚ,
      Trace (block.compile 0 ++ [.halt 0]) (m.atPC 0) c run ∧
      (run (Fin.last c)).output = some 0 ∧
      Staged row price m (run (Fin.last c)).memory B ∧
      ∀ i, scalarBound (stageWidth n H L B) (run i) := by
  obtain ⟨r,hr,hs⟩ := pivotStep_eval D J price f hD hJ
  have he : r = row := Option.some.inj (hr.symm.trans hrun)
  subst r
  obtain ⟨t,c,hc,run,out⟩ := block_spec D J price f row hrun hs m H L B hm hlocal hB hn hi ho hsep hraw hlog hprice
  obtain ⟨tr,steps,halt,mem,hbits⟩ := run.halted_trace (tag := 0)
  exact ⟨c+1,by omega,tr,steps,halt,by rw [mem]; exact out,hbits⟩

end PivotStageRAM
end Geometry
end LinearProgramming
end Optimization
end OAI

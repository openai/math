import OAI.Optimization.LinearProgramming.Geometry.BorderCandidate
import OAI.Optimization.LinearProgramming.Geometry.BorderMarkedExchange
import OAI.Optimization.LinearProgramming.Geometry.OracleUnique

/-! The physical ABI certificate at the live query of a complete candidate
iteration. The ordinary theorem supplies the cost and all geometric postconditions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Contract OracleSegments Matrix BorderScatter

variable {r s n k : ℕ}

private theorem marked_unpack (mark : QueryMark ℚ) {P : ℚ → Prop} (o : ScalarOracle ℚ)
    (m : Memory ℚ) (h : Contract.History ℚ) (hm : m.AllData P) :
    ∃ k t, MarkedRuns mark unpack o (Memory.AllData P) m h k t h := by
  unfold unpack
  let t := loadTagState m
  have tag := MarkedRuns.core (mark := mark) (loadTag_spec m hm) o h
  by_cases stop : t.data 2<t.data 3
  · have run := MarkedRuns.core (mark := mark) (restart_spec t tag.finish) o h
    exact ⟨_,_,tag.seq (MarkedRuns.branchTrue (c := .scalarLT 2 3) (b := (Segment.core value).seq (.core BorderScatter.append))
      (by simpa only [Cond.test,decide_eq_true_eq] using stop) run)⟩
  · have read := MarkedRuns.core (mark := mark) (value_spec t tag.finish) o h
    have write := MarkedRuns.core (mark := mark) (append_spec (valueState t) read.finish) o h
    exact ⟨_,_,tag.seq (MarkedRuns.branchFalse (c := .scalarLT 2 3) (a := .core restart)
      (by simpa only [Cond.test,decide_eq_false_iff_not] using stop) (read.seq write))⟩

private theorem marked_candidate_from_request (mark : QueryMark ℚ) {P : ℚ → Prop} (o : ScalarOracle ℚ)
    (m : Memory ℚ) (h : Contract.History ℚ) (hm : m.AllData P) (h0 : P 0)
    (request : (loadState m).data 27 ≠ (loadState m).data 2 →
      ∃ z c hist, MarkedRuns mark submit o (Memory.AllData P) (loadState m) h c z hist) :
    ∃ t k hist, MarkedRuns mark candidate o (Memory.AllData P) m h k t hist := by
  have loadRun := MarkedRuns.core (mark := mark) (load_spec m hm h0) o h
  by_cases zero : (loadState m).data 27=(loadState m).data 2
  · have app := MarkedRuns.core (mark := mark) (append_spec (loadState m) loadRun.finish) o h
    refine ⟨appendState (loadState m),4+(1+(1+9)),h,?_⟩
    unfold candidate nonzero
    exact loadRun.seq (MarkedRuns.branchFalse (c := .scalarLT 27 2) (by simp [Cond.test,zero])
      (MarkedRuns.branchFalse (c := .scalarLT 2 27) (by simp [Cond.test,zero]) app))
  · obtain ⟨z,c,hist,send⟩ := request zero
    obtain ⟨k,t,unpacked⟩ := marked_unpack mark o z hist send.finish
    have action := send.seq unpacked
    rcases lt_or_gt_of_ne zero with lt|gt
    · refine ⟨t,4+(1+(c+k)+1),hist,?_⟩
      unfold candidate nonzero
      exact loadRun.seq (MarkedRuns.branchTrue (c := .scalarLT 27 2)
        (by simp [Cond.test,lt]) action)
    · refine ⟨t,4+(1+(1+(c+k)+1)),hist,?_⟩
      unfold candidate nonzero
      exact loadRun.seq (MarkedRuns.branchFalse (c := .scalarLT 27 2) (by simp [Cond.test,gt.not_gt])
        (MarkedRuns.branchTrue (c := .scalarLT 2 27) (by simp [Cond.test,gt]) action))

theorem candidate_runs_marked {L : Layout r n} {original m : Memory ℚ} (P A : ℚ → Prop) (o : ScalarOracle ℚ)
    (h : Contract.History ℚ) (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (J : Fin k → Fin n) (price : Fin n → ℚ) (hr : k+1 ≤ r) (hrn : r ≤ n) (src : Sources L original D hr J price)
    (j : Fin n) (v : Fin n → ℚ) (hm : m.AllData P) (hAP : ∀q,A q → P q) (hz : A 0)
    (hn : ∀i ≤ n,P (i:ℚ)) (responds : Responds D E A o)
    (active : ScanReady L original (borderedMinor (D.submatrix (Fin.castLE hr) id) J) price A j.val v m) :
    let raw := borderedMinor (D.submatrix (Fin.castLE hr) id) J
    let next (w : Fin n → ℚ) (t : Memory ℚ) := ScanReady L original raw price A (j.val+1) w t
    if raw j = 0 then ∃ t c, c ≤ candidateCost k n ∧ MarkedRuns MinorSite candidate o (Memory.AllData P) m h c t h ∧ next v t
    else ∃ ans : Option ℚ, ∃ t c, c ≤ candidateCost k n ∧ MarkedRuns MinorSite candidate o (Memory.AllData P) m h c t
        ((keyPacket D E (pivotKey J j),reply ans)::h) ∧
      match ans with | none => ScanStopped L original t | some q => next (Function.update v j q) t := by
  let raw := borderedMinor (D.submatrix (Fin.castLE hr) id) J
  let b := loadState m
  have eLoad := load_spec m hm (hAP 0 hz)
  have hold : ScanReady L original raw price A j.val v b := active.hold (scanLoad active)
  obtain ⟨raw27,_,zero2,zero29⟩ := loaded_inputs active j rfl (src.raw j) (src.prices j)
  have request (nz : b.data 27 ≠ b.data 2) :
      ∃ z c hist, MarkedRuns MinorSite submit o (Memory.AllData P) b h c z hist := by
    have nonzeroMinor : circuitMinor (D.submatrix (Fin.castLE hr) id) J j ≠ 0 := by
      rw [←borderedMinor_eq]
      intro zero
      exact nz (raw27.trans (zero.trans zero2.symm))
    have idx (a : ℕ) (ha : 128 ≤ a) (hn : a≠139) : b.index a=original.index a := hold.indices a ha hn
    have bk := (idx 128 (by decide) (by decide)).trans src.ready.prefixCount
    have bn := (idx 130 (by decide) (by decide)).trans src.ready.width
    have bs := (idx 144 (by decide) (by decide)).trans src.ready.scratchAddr
    have bp := (idx 136 (by decide) (by decide)).trans src.ready.pivotAddr
    have bJ (i : Fin k) : b.index (b.index 136+i.val)=(J i).val := by
      rw [bp,idx _ (by have := L.pivots_ge; omega) (by have := L.pivots_ge; omega),src.ready.pivotData]
    have sl := L.source_ge; have sp := L.source_end; have pt := L.prices_end; have tr := L.triples_end
    have rd := L.rounded_end; have ab := L.answers_end; have ps := L.pivots_ge
    obtain ⟨ans,z,c,_,send,_,_⟩ := submit_runs_marked b P o h D E J j hr hrn nonzeroMinor L.scratch
      bk bn hold.cursor bs (by omega) (by rw [bp]; omega) bJ eLoad.safe_end hn (hAP 0 hz)
      (by simpa using hn 1 (by omega)) zero2 zero29 A hAP responds
    exact ⟨z,c,_,send⟩
  obtain ⟨t,c,hist,marked⟩ := marked_candidate_from_request MinorSite o m h hm (hAP 0 hz) request
  have transport {u : Memory ℚ} {l : ℕ} {f : Contract.History ℚ}
      (run : Runs candidate o (Memory.AllData P) m h l u f) :
      MarkedRuns MinorSite candidate o (Memory.AllData P) m h l u f := by
    obtain ⟨rfl,rfl,rfl⟩ := run.unique marked.forget
    exact marked
  have old := candidate_runs P A o h D E J price hr hrn src j v hm hAP hz hn responds active
  dsimp only at old ⊢
  by_cases zero : raw j=0
  · rw [ite_eq_left zero] at old ⊢
    obtain ⟨u,l,hl,run,final⟩ := old
    exact ⟨u,l,hl,transport run,final⟩
  · rw [ite_eq_right zero] at old ⊢
    obtain ⟨ans,u,l,hl,run,final⟩ := old
    exact ⟨ans,u,l,hl,transport run,final⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Geometry.OracleSegments
import OAI.Optimization.LinearProgramming.Geometry.BorderScatter

/-! Fixed sign and reply control flow for each bordered-minor candidate. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Contract OracleSegments BorderScatter

/-- A scalar equality test built out of the available strict comparisons. -/
def nonzero (yes no : Segment) : Segment :=
  .branch (.scalarLT 27 2) yes (.branch (.scalarLT 2 27) yes no)

theorem nonzero_equal {o : ScalarOracle ℚ} {P : Memory ℚ → Prop} {m t : Memory ℚ}
    {h f : Contract.History ℚ} {c : ℕ} (yes no : Segment)
    (he : m.data 27=m.data 2) (run : Runs no o P m h c t f) : Runs (nonzero yes no) o P m h (1+(1+c)) t f :=
  Runs.branchFalse (by simp [Cond.test,he]) (Runs.branchFalse (by simp [Cond.test,he]) run)

theorem nonzero_different {o : ScalarOracle ℚ} {P : Memory ℚ → Prop} {m t : Memory ℚ}
    {h f : Contract.History ℚ} {c : ℕ} (yes no : Segment)
    (he : m.data 27 ≠ m.data 2) (run : Runs yes o P m h c t f) :
    ∃ d ≤ 3,Runs (nonzero yes no) o P m h (d+c) t f := by
  rcases lt_or_gt_of_ne he with lt | gt
  · exact ⟨2,by decide,by simpa [nonzero,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      (Runs.branchTrue (b := Segment.branch (.scalarLT 2 27) yes no) (c := .scalarLT 27 2)
        (by simp [Cond.test,lt]) run)⟩
  · exact ⟨3,by decide,by simpa [nonzero,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      (Runs.branchFalse (a := yes) (c := .scalarLT 27 2) (by simp [Cond.test,gt.not_gt])
        (Runs.branchTrue (b := no) (c := .scalarLT 2 27) (by simp [Cond.test,gt]) run))⟩

def unpack : Segment := (Segment.core loadTag).seq (.branch (.scalarLT 2 3)
  (.core restart) ((Segment.core value).seq (.core BorderScatter.append)))

theorem unpack_restart {o : ScalarOracle ℚ} {P : Memory ℚ → Prop} {m t e : Memory ℚ}
    {h : Contract.History ℚ} {a b : ℕ} (tag : Runs (.core loadTag) o P m h a t h)
    (hz : t.data 2=0) (hr : t.data 3=1) (go : Runs (.core restart) o P t h b e h) :
    Runs unpack o P m h (a+(1+b+1)) e h := by
  unfold unpack
  exact tag.seq (Runs.branchTrue (c := .scalarLT 2 3) (by simp [Cond.test,hz,hr]) go)

theorem unpack_value {o : ScalarOracle ℚ} {P : Memory ℚ → Prop} {m t w e : Memory ℚ}
    {h : Contract.History ℚ} {a b c : ℕ} (tag : Runs (.core loadTag) o P m h a t h)
    (hz : t.data 2=0) (hr : t.data 3=0) (read : Runs (.core value) o P t h b w h)
    (go : Runs (.core BorderScatter.append) o P w h c e h) :
    Runs unpack o P m h (a+(1+(b+c))) e h := by
  unfold unpack
  exact tag.seq (Runs.branchFalse (c := .scalarLT 2 3) (by simp [Cond.test,hz,hr]) (read.seq go))

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI

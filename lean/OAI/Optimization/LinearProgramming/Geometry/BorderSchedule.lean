import OAI.Optimization.LinearProgramming.Geometry.BorderTailColumns
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixTrace
import OAI.Optimization.LinearProgramming.Geometry.MinorKeys

/-! Match the instruction-level candidate traversal with the proved geometric query tree,
including a partial transcript when a service returns the restart tag. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open Matrix

variable {n k : ℕ} {κ : Type*}

/-- Every answering candidate is outside the previous pivot set. This is what makes
the per-stage key-to-value assignment well-defined even for a history-dependent service. -/
theorem answering_key_injective (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (i j : Fin n) (hi : borderedMinor D J i ≠ 0) (eq : pivotKey J i=pivotKey J j) : i=j := by
  have mem : i ∈ (pivotKey J j).2 := eq ▸ Finset.mem_insert_self i _
  rcases Finset.mem_insert.mp mem with h | h
  · exact h
  · obtain ⟨p,-,he⟩ := Finset.mem_image.mp h
    have hc : Fin.last k ≠ p.castSucc := Fin.ne_of_gt (Fin.castSucc_lt_last p)
    apply False.elim; apply hi
    rw [borderedMinor_eq]
    exact Matrix.det_zero_of_column_eq hc (fun q => by simp [he])

/-- Extend all replies of one completed scan to the total assignment expected by the
correctness theorem. The choice on keys outside the valid candidate list is immaterial. -/
noncomputable def stageExtension (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (values : Fin n → ℚ) (key : PivotKey n) : ℚ := by
  classical
  exact if h : ∃ i, borderedMinor D J i ≠ 0 ∧ pivotKey J i=key then values h.choose else 0

theorem stageExtension_at (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (values : Fin n → ℚ) (j : Fin n) (hn : borderedMinor D J j ≠ 0) :
    stageExtension D J values (pivotKey J j)=values j := by
  classical
  have good : ∃ i, borderedMinor D J i ≠ 0 ∧ pivotKey J i=pivotKey J j := ⟨j,hn,rfl⟩
  unfold stageExtension
  rw [dite_eq_left good]
  exact congrArg values (answering_key_injective D J _ j good.choose_spec.1 good.choose_spec.2)

def candidateAnswers (raw : Fin n → ℚ) (key : Fin n → κ) (values : Fin n → ℚ) (j : ℕ) :
    List (κ × ℚ) := (tailColumns raw j).map fun a => (key a,values a)

private theorem read_consistency (key : Fin n → κ) (L : List (Fin n)) (disjoint : L.Nodup)
    (start out : Fin n → ℚ) {xs} (run : MinorQuery.Run (MinorQuery.readColumns key L start) xs (.inr out)) :
    xs=L.map (fun i => (key i,out i)) ∧ ∀ i, i ∉ L → out i=start i := by
  induction L generalizing start xs with
  | nil =>
    cases run
    exact ⟨rfl,fun _ _ => rfl⟩
  | cons j js ih =>
    change MinorQuery.Run (.query (key j) (fun q => MinorQuery.readColumns key js (Function.update start j q))) _ _ at run
    cases run with
    | answer _ _ q tail =>
      obtain ⟨hr,ht⟩ := ih (List.nodup_cons.mp disjoint).2 _ tail
      have last := ht j (List.nodup_cons.mp disjoint).1
      simp only [Function.update_self] at last
      refine ⟨by simp [hr,last],?_⟩
      intro i hi
      have past := ht i (fun hm => hi (List.mem_cons_of_mem _ hm))
      have ne : i≠j := by rintro rfl; simp at hi
      simpa [ne] using past

/-- A successful actual read pass yields the exact row, exact original query transcript,
and the total compressed assignment reproducing that execution. -/
theorem step_of_scanned (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n) (price : Fin n → ℚ)
    (hD : LinearIndependent ℚ D.row) (hJ : (D.submatrix Fin.castSucc J).det ≠ 0)
    (values : Fin n → ℚ) {xs}
    (run : MinorQuery.Run (MinorQuery.readColumns (pivotKey J) (tailColumns (borderedMinor D J) 0) 0)
      xs (.inr values)) :
    let f := stageExtension D J values
    ∃ row : PivotRow n, MinorQuery.Run (pivotStep D J price) xs (.inr (some row)) ∧
      MinorQuery.eval f (pivotStep D J price)=some row ∧
      row.raw=borderedMinor D J ∧ row.logs=values := by
  let cols := tailColumns (borderedMinor D J) 0
  let f := stageExtension D J values
  have nodup : cols.Nodup := List.Nodup.filter _ (List.nodup_finRange n)
  obtain ⟨log,-⟩ := read_consistency (pivotKey J) cols nodup 0 values run
  have agrees : ∀e∈xs,f e.1=e.2 := by
    intro e he
    rw [log] at he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    exact stageExtension_at D J values i (by simpa [cols,tailColumns] using hi)
  obtain ⟨row,hr,-⟩ := pivotStep_eval D J price f hD hJ
  have compute := run.eval_of_extends f agrees
  let finish (v : Fin n → ℚ) := MinorQuery.done (κ := PivotKey n)
    ((cols.argmax (fun j => v j-price j)).map (fun i => (⟨i,borderedMinor D J,v⟩ : PivotRow n)))
  have form : pivotStep D J price = (MinorQuery.readColumns (pivotKey J) cols 0).bind finish := by
    have tab : (Vector.ofFn (borderedMinor D J)).get = borderedMinor D J := by
      funext i
      exact Vector.getElem_ofFn (f := borderedMinor D J) i.isLt
    dsimp only [pivotStep]
    rw [tab]
    rfl
  have original := hr
  rw [form,MinorQuery.eval_bind,compute] at hr
  change ((cols.argmax (fun j => values j-price j)).map (fun i => (⟨i,borderedMinor D J,values⟩ : PivotRow n))) = some row at hr
  have all := run.bind_answer (k := finish) (MinorQuery.Run.done ((cols.argmax (fun j => values j-price j)).map (fun i => (⟨i,borderedMinor D J,values⟩ : PivotRow n))))
  refine ⟨row,?_,?_,?_,?_⟩
  · simpa only [form,List.append_nil,hr] using all
  · exact original
  · cases h : cols.argmax (fun j => values j-price j) <;> simp [h] at hr
    cases hr
    rfl
  · cases h : cols.argmax (fun j => values j-price j) <;> simp [h] at hr
    cases hr
    rfl

/-- A restart in the read pass is reported at the same key by the whole pivot step. -/
theorem step_of_restarted (D : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n) (price : Fin n → ℚ)
    {xs key} (run : MinorQuery.Run (MinorQuery.readColumns (pivotKey J) (tailColumns (borderedMinor D J) 0) 0)
      xs (.inl key)) : MinorQuery.Run (pivotStep D J price) xs (.inl key) := by
  unfold pivotStep
  apply MinorQuery.Run.bind_restart
  have tab : (Vector.ofFn (borderedMinor D J)).get = borderedMinor D J := by
    funext i
    exact Vector.getElem_ofFn (f := borderedMinor D J) i.isLt
  rw [tab]
  exact run

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Geometry.LabelResult
import OAI.Optimization.LinearProgramming.Geometry.ExecutedPrefix
import OAI.Optimization.LinearProgramming.Geometry.NamedRequests
import OAI.Optimization.LinearProgramming.Geometry.WirePredicates
import OAI.Optimization.LinearProgramming.Geometry.MinorQuery

/-! Canonical public nonzero-minor indices and the observed scalar packets provide
a matrix-independent account of agreement between assignments and a geometric query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Contract OracleSpec Matrix Compression BorderBatch
open scoped Matrix

variable {r s n : ℕ}

namespace LabelRAM

/-- Successful responses constrain the final label for every full clipped assignment
that agrees with all scalar answers in the actual transcript. -/
theorem Result.completed_correct {packet : PivotKey n → List ℚ} {D : Matrix (Fin r) (Fin n) ℚ}
    {q : PriceGame.Query n} {before final : Contract.History ℚ} {t : Memory ℚ}
    (result : Result packet D q before t final) (status : t.index 139=0)
    (E : Matrix (Fin s) (Fin n) ℚ) (hD : LinearIndependent ℚ D.row)
    (hE : LinearIndependent ℚ E.row) (hrank : r+s=n) (hDE : D*Eᵀ=0) :
    ∃ xs : List (PivotKey n × ℚ), xs.length ≤ r*n ∧
      final = PivotPrefixRAM.answeredHistory packet xs before ∧
      ∀ f : Compression.NonzeroPairMinor D E → ℚ,
        FourLogAccuracy (geoCutoff n : ℝ) (pairMinorLog D E) (fun u => (f u : ℝ)) →
        (∀ e ∈ xs, prefixAssignment D E f e.1=e.2) →
        ValidNearLabel (minorCircuitFamily D (prefixAssignment D E f)) true q (decide (t.data 19=1)) ∧
        ValidNearLabel (minorCircuitFamily E (dualPrefixAssignment D E f)) false q (decide (t.data 19=1)) := by
  cases result with
  | restarted _ _ _ _ flag => omega
  | completed xs rows requests history _ answer =>
    refine ⟨xs,by simpa [MinorQuery.restartCost] using requests.call_bound (pivotPrefix_bounded ..),history,?_⟩
    intro f hclip hread
    have labels := completedPrefix_circuit_labels D E hD hE hrank hDE f hclip q rows xs requests hread
    rw [show OracleSpec.MinorLog.threshold n=geoCutoff n by rfl] at answer
    split at answer <;> rename_i hb <;> simpa [answer,hb] using labels

end LabelRAM

private theorem namedAnswered (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (xs : List (PivotKey n × ℚ)) (valid : ∀ e ∈ xs, ∃ u, Canonical.checkedPrimalMinor D E e.1=some u) :
    NamedTraffic D E (PivotPrefixRAM.answeredHistory (keyPacket D E) xs []) := by
  intro w hw
  simp only [PivotPrefixRAM.answeredHistory,List.append_nil,List.mem_reverse,List.mem_map] at hw
  obtain ⟨e,he,rfl⟩ := hw
  obtain ⟨u,h⟩ := valid e he
  exact ⟨interfaceIndex D E u,by simp [keyPacket,h,packet],Or.inr ⟨e.2,rfl⟩⟩

/-- All successfully answered queries, and the final query on an interrupted execution,
are valid canonical requests. The paper's `r n` bound counts the final restart request. -/
theorem LabelRAM.Result.named_traffic {D : Matrix (Fin r) (Fin n) ℚ} (E : Matrix (Fin s) (Fin n) ℚ)
    {q : PriceGame.Query n} {m : Memory ℚ} {hist : Contract.History ℚ}
    (done : LabelRAM.Result (keyPacket D E) D q [] m hist) : NamedTraffic D E hist ∧ hist.length≤r*n := by
  cases done with
  | completed xs rows trace events status answer =>
    rw [events]
    refine ⟨namedAnswered D E xs (prefix_run_named D E q.prices le_rfl trace).1,?_⟩
    simpa [PivotPrefixRAM.answeredHistory,MinorQuery.restartCost] using trace.call_bound (pivotPrefix_bounded ..)
  | restarted xs k trace events status =>
    rw [events]
    have all := prefix_run_named D E q.prices le_rfl trace
    refine ⟨?_,?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|h
      · obtain ⟨u,hu⟩ := all.2
        exact ⟨interfaceIndex D E u,by simp [keyPacket,hu,packet],Or.inl rfl⟩
      · exact namedAnswered D E xs all.1 w h
    · simpa [PivotPrefixRAM.answeredHistory,MinorQuery.restartCost] using trace.call_bound (pivotPrefix_bounded ..)

/-- Extract the new canonical transcript even when a geometric call starts with an
arbitrary history inherited from its caller. -/
theorem LabelRAM.Result.fresh_traffic {D : Matrix (Fin r) (Fin n) ℚ} (E : Matrix (Fin s) (Fin n) ℚ)
    {q : PriceGame.Query n} {m : Memory ℚ} {before final : Contract.History ℚ}
    (done : LabelRAM.Result (keyPacket D E) D q before m final) :
    ∃ fresh, final=fresh++before ∧ NamedTraffic D E fresh ∧ fresh.length≤r*n := by
  have freshRun : ∃ fresh, final=fresh++before ∧ LabelRAM.Result (keyPacket D E) D q [] m fresh := by
    cases done with
    | completed xs rows requests history status output =>
      refine ⟨PivotPrefixRAM.answeredHistory (keyPacket D E) xs [],?_,.completed xs rows requests rfl status output⟩
      simpa only [PivotPrefixRAM.answeredHistory,List.append_nil] using history
    | restarted xs k requests history status =>
      refine ⟨(keyPacket D E k,[1])::PivotPrefixRAM.answeredHistory (keyPacket D E) xs [],?_,.restarted xs k requests rfl status⟩
      simpa only [PivotPrefixRAM.answeredHistory,List.append_nil,List.cons_append] using history
  obtain ⟨fresh,eq,run⟩ := freshRun
  exact ⟨fresh,eq,run.named_traffic E⟩

/-- Under every assignment satisfying the four-term error bound and agreeing with the
transmitted packets, the scalar return agrees with both one-sided circuit-envelope tests. -/
theorem LabelRAM.Result.wire_correct {D : Matrix (Fin r) (Fin n) ℚ} (E : Matrix (Fin s) (Fin n) ℚ)
    {q : PriceGame.Query n} {m : Memory ℚ} {hist : Contract.History ℚ}
    (done : LabelRAM.Result (keyPacket D E) D q [] m hist) (ok : m.index 139=0)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (hrank : r+s=n) (hDE : D*Eᵀ=0)
    (F : MinorLog.Index D E → ℚ)
    (hclip : FourLogAccuracy (geoCutoff n : ℝ) (pairMinorLog D E) (fun u => (F (interfaceIndex D E u) : ℝ)))
    (agree : AgreesOnReplies D E hist F) :
    let f := fun u => F (interfaceIndex D E u)
    ValidNearLabel (minorCircuitFamily D (prefixAssignment D E f)) true q (decide (m.data 19=1)) ∧
      ValidNearLabel (minorCircuitFamily E (dualPrefixAssignment D E f)) false q (decide (m.data 19=1)) := by
  let f := fun u => F (interfaceIndex D E u)
  cases done with
  | restarted _ _ _ _ flag => omega
  | completed xs rows trace history _ output =>
    have known := (prefix_run_named D E q.prices le_rfl trace).1
    have prefixAgrees : ∀ e ∈ xs, prefixAssignment D E f e.1=e.2 := by
      intro e he
      obtain ⟨u,hu⟩ := known e he
      rw [← Canonical.checkedPrimalMinor_value,hu]
      apply agree (interfaceIndex D E u) e.2
      rw [history]
      simp only [PivotPrefixRAM.answeredHistory,List.append_nil,List.mem_reverse,List.mem_map]
      exact ⟨e,he,by simp [keyPacket,hu,packet]⟩
    have result := completedPrefix_circuit_labels D E hD hE hrank hDE f hclip q rows xs trace prefixAgrees
    rw [show OracleSpec.MinorLog.threshold n=geoCutoff n by rfl] at output
    split at output <;> rename_i decision <;> simpa [f,output,decision] using result

end Geometry
end LinearProgramming
end Optimization
end OAI

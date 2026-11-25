import OAI.Optimization.LinearProgramming.Geometry.ConcreteOracle
import OAI.Optimization.LinearProgramming.Geometry.WireConsensus
import OAI.Optimization.LinearProgramming.Geometry.OracleUnique
import OAI.Optimization.LinearProgramming.Geometry.MarkedNames
import OAI.Optimization.LinearProgramming.Geometry.MarkedLabelControl
import OAI.Optimization.LinearProgramming.Geometry.BorderMarkedBatch

/-! The true prefix-query local certificates survive the entire geometric label call. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Contract OracleSpec BorderBatch OracleSegments

/-- Align the marked prefix proof with the existing numerical computation by
uniqueness of the actual register, history and cost at their common boundary. -/
theorem LabelRAM.Split.marked {mark : QueryMark ℚ} {batch : Segment} {o : ScalarOracle ℚ} {P : Memory ℚ → Prop}
    {base t u : Memory ℚ} {old final mid : Contract.History ℚ} {k c : ℕ}
    (splitRun : Split batch o P base old k t final)
    (prefixRun : MarkedRuns mark (PivotPrefixRAM.program batch) o P base old c u mid) :
    MarkedRuns mark (segment batch) o P base old k t final := by
  obtain ⟨state,k₀,k₁,rfl,pre,post⟩ := splitRun
  obtain ⟨rfl,rfl,rfl⟩ := prefixRun.forget.unique pre
  exact prefixRun.seq (MarkedRuns.of_coreOnly (LabelControl.continuation_coreOnly _) post)

/-- Every scalar exchange in this very label computation carries the architectural
preconditions for an ordinary-RAM minor handler and an index for its actual words. -/
theorem geometricLabelProcedure_marked {r s n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (q : PriceGame.Query n) (o : ScalarOracle ℚ) (base : Memory ℚ) (old : Contract.History ℚ)
    (x : LabelInput.Buffers r s n) (hdr : LabelInput.Header x D E q.prices q.index base)
    (e g H : ℕ) (hD : LinearIndependent ℚ D.row) (hrn : r≤n) (safe : RowRAM.Within H base)
    (hmat : ∀ i j, ratBits (D i j)≤e) (hprice : ∀ j, ratBits (q.prices j)≤e)
    (service : Responds D E (fun v => ratBits v≤g) o) :
    ∃ t final k, k+3≤LabelRAM.time r n (batchTime r n) ∧
      MarkedRuns (namedMark D E MinorSite) geometricLabelProcedure o (RowRAM.Within (geometricLabelWidth r n e g H))
        base old k t final ∧ (∀ a, 64≤a → a<x.layout.triples → t.data a=base.data a) ∧
      LabelRAM.HeaderPreserved base t ∧ LabelRAM.Result (keyPacket D E) D q old t final := by
  obtain ⟨t,final,k,time,_,keep,header,result,splitRun⟩ :=
    geometricLabelProcedure_run D E q o base old x hdr e g H hD hrn safe hmat hprice service
  obtain ⟨u,mid,c,_,flagged,_⟩ := prefix_runs_marked D E q.prices base e g H o old hdr.border hD hrn
    hmat hprice service safe
  have markedPrefix : MarkedRuns MinorSite (PivotPrefixRAM.program batchProgram) o
      (RowRAM.Within (geometricLabelWidth r n e g H)) base old c u mid :=
    flagged.weaken (fun _ h j => (h j).trans (le_max_left _ _))
  obtain ⟨fresh,shape,legal,_⟩ := result.fresh_traffic E
  exact ⟨t,final,k,time,mark_named_segment (splitRun.marked markedPrefix) ⟨fresh,shape,legal⟩,keep,header,result⟩

end Geometry
end LinearProgramming
end Optimization
end OAI

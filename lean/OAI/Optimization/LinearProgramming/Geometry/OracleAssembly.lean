import OAI.Optimization.LinearProgramming.Geometry.LabelResult
import OAI.Optimization.LinearProgramming.Geometry.LabelRAMCode
import OAI.Optimization.LinearProgramming.Geometry.AfterPrefix
import OAI.Optimization.LinearProgramming.Geometry.LabelBits
import OAI.Optimization.LinearProgramming.Geometry.LabelControl
import OAI.Optimization.LinearProgramming.PriceGame.Model
import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixRAM
import OAI.Optimization.LinearProgramming.Geometry.PivotAlwaysFrame

/-! Assembly of the physical prefix collector, postprocessing RAM, restart branch,
and tagged exit for a designated price query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix RAM RAM.Block Contract OracleSegments
open scoped Matrix

namespace LabelRAM

variable {r s n : ℕ}

private theorem postInputs (base m : Memory ℚ) {a B : ℕ} (rows : Fin a → PivotRow n)
    (price : Fin n → ℚ) (stored : PivotPrefixRAM.Stored base m rows price B)
    (i : Fin n) (free : ℕ) (hdr : PostPivotLayout.Inputs r (base.index 134) free i base) :
    PostPivotLayout.Inputs r (base.index 134) free i (LabelControl.marker m) := by
  have same (a : ℕ) (lo : 129≤a) (hi : a≤149) (h₁ : a≠135) (h₂ : a≠137) (h₃ : a≠139) :
      (LabelControl.marker m).index a=base.index a := by
    simpa [LabelControl.marker, show a≠6 by omega] using stored.permanent a lo hi h₁ h₂ h₃
  exact ⟨(same 129 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdr.rows,
    (same 130 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdr.cols,
    same 134 (by decide) (by decide) (by decide) (by decide) (by decide),
    (same 146 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdr.designation,
    (same 149 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdr.freeBase⟩

/-- Safe global register and time budgets for the actual linked instruction stream. -/
def width (r n L extra H : ℕ) : ℕ :=
  max (H+r*PivotPrefixRAM.stepWidth n L (OracleSpec.MinorLog.threshold n) extra)
    (afterPrefixBits r n (8+2*(OracleSpec.MinorLog.threshold n+4)))

/-- The exact boundary between a true query-emitting prefix and the core-only
numerical suffix. It allows independent per-exchange certificates to be attached
to the very same computation, without repeating the numerical proof. -/
def Split (batch : Segment) (o : ScalarOracle ℚ) (P : Memory ℚ → Prop)
    (base : Memory ℚ) (old : Contract.History ℚ) (k : ℕ) (t : Memory ℚ) (final : Contract.History ℚ) : Prop :=
  ∃ u k₀ k₁, k=k₀+k₁ ∧ Runs (PivotPrefixRAM.program batch) o P base old k₀ u final ∧
    Runs (LabelControl.continuation afterPrefixBlock) o P u final k₁ t final

/-- Each accepted prefix is extended by exactly the materialized rational matrix. A
restart skips every Gram and minimization step. -/
theorem segment_run (batch : Segment) (o : ScalarOracle ℚ) (packet : PivotKey n → List ℚ)
    (D : Matrix (Fin r) (Fin n) ℚ) (q : PriceGame.Query n) (base : Memory ℚ) (hist₀ : Contract.History ℚ)
    (Aux : Memory ℚ → Contract.History ℚ → Prop) (L extra C H free : ℕ)
    (layout : PivotPrefixRAM.Layout base r n (OracleSpec.MinorLog.threshold n)) (hD : LinearIndependent ℚ D.row)
    (hdr : PostPivotLayout.Inputs r (base.index 134) free q.index base) (hfree : base.index 134+r*n≤free)
    (hb : RowRAM.Within H base) (stable : PivotPrefixRAM.FrameStable base r n Aux) (aux : Aux base hist₀)
    (action : PivotPrefixRAM.BatchSound batch o packet base D q.prices (OracleSpec.MinorLog.threshold n) L extra C Aux) :
    ∃ t final k, k+3 ≤ time r n C ∧
      Runs (segment batch) o (RowRAM.Within (width r n L extra H)) base hist₀ k t final ∧
      (∃ u, Aux u final ∧ Preserved r n free u t) ∧ HeaderPreserved base t ∧ Result packet D q hist₀ t final ∧
      Split batch o (RowRAM.Within (width r n L extra H)) base hist₀ k t final := by
  let W := width r n L extra H
  obtain ⟨u,final,k,hk,pre,auxU,res⟩ :=
    PivotPrefixRAM.run batch o packet D q.prices base hist₀ Aux layout hD hb stable aux action
  have prefixRun : Runs (PivotPrefixRAM.program batch) o (RowRAM.Within W) base hist₀ k u final :=
    pre.weaken fun _ h j => (h j).trans (le_max_left _ _)
  have safe : RowRAM.Within W u := prefixRun.finish
  have markSafe : RowRAM.Within W (LabelControl.marker u) := safe
  cases res with
  | restarted xs key a ha rows requests hist status stored =>
    have endRun := LabelControl.continue_restart afterPrefixBlock o (RowRAM.Within W) u final safe markSafe status
    refine ⟨LabelControl.marker u,final,k+2,by unfold time; omega,prefixRun.seq endRun,
      ⟨u,auxU,fun _ _ _ => rfl,?_⟩,?_,.restarted xs key requests hist ?_,
      ⟨u,k,2,rfl,prefixRun,endRun⟩⟩
    · intro j hj; simp [LabelControl.marker,show j≠6 by omega]
    · intro j hj hi h₁ h₂ h₃
      simpa [LabelControl.marker,show j≠6 by omega] using stored.permanent j hj hi h₁ h₂ h₃
    · simpa [LabelControl.marker] using status
  | completed xs rows requests hist status stored =>
    let M := roundedPivotMatrix rows q.prices (OracleSpec.MinorLog.threshold n)
    have table : uniformRect r n (base.index 134) (LabelControl.marker u) = M := by
      funext i j; exact stored.rounded i j
    have hr := prefix_run_rounded_independent D q.prices le_rfl requests (OracleSpec.MinorLog.threshold n)
    obtain ⟨t,l,hl,post,value,frame,idx⟩ := afterPrefixBlock_spec M q.index (LabelControl.marker u)
      (base.index 134) free (8+2*(OracleSpec.MinorLog.threshold n+4)) W layout.rowsHigh hfree
      (postInputs base u rows q.prices stored q.index free hdr) markSafe table hr
      (roundedPivotMatrix_ratBits rows q.prices (OracleSpec.MinorLog.threshold n)) (le_max_right _ _)
    have endRun := LabelControl.continue_success afterPrefixBlock o (RowRAM.Within W) u t final l safe status post
    refine ⟨t,final,k+(l+3),by unfold time; omega,prefixRun.seq endRun,
      ⟨u,auxU,frame,?_⟩,?_,.completed xs rows requests hist ?_ value,
      ⟨u,k,l+3,rfl,prefixRun,endRun⟩⟩
    · intro j hj; simpa [LabelControl.marker,show j≠6 by omega] using idx j hj
    · intro j hj hi h₁ h₂ h₃
      exact (idx j (by omega)).trans (by simpa [LabelControl.marker,show j≠6 by omega] using stored.permanent j hj hi h₁ h₂ h₃)
    · exact (idx 139 (by decide)).trans (by simpa [LabelControl.marker] using status)


/-- The terminal comparison writes only its private address register. -/
theorem Result.marker {packet : PivotKey n → List ℚ} {D : Matrix (Fin r) (Fin n) ℚ}
    {q : PriceGame.Query n} {before final : Contract.History ℚ} {t : Memory ℚ}
    (res : Result packet D q before t final) : Result packet D q before (LabelControl.marker t) final := by
  cases res with
  | completed xs rows trace hist stat out =>
    exact .completed xs rows trace hist (by simpa [LabelControl.marker] using stat) out
  | restarted xs key trace hist stat =>
    exact .restarted xs key trace hist (by simpa [LabelControl.marker] using stat)

theorem Preserved.marker {free : ℕ} {pre t : Memory ℚ} (p : Preserved r n free pre t) :
    Preserved r n free pre (LabelControl.marker t) := by
  refine ⟨p.data,fun j hj => ?_⟩
  simpa [LabelControl.marker,show j≠6 by omega] using p.index j hj

/-- Turn the linked segment into a terminal oracle run. The tag, arithmetic answer,
scalar/register frame, and exact history all refer to that same final configuration. -/
theorem program_run_of_segment {batch : Segment} {o : ScalarOracle ℚ} {W k : ℕ}
    {packet : PivotKey n → List ℚ} {D : Matrix (Fin r) (Fin n) ℚ} {q : PriceGame.Query n}
    {hist final : Contract.History ℚ} {base pre t : Memory ℚ} {free : ℕ}
    (run : Runs (segment batch) o (RowRAM.Within W) base hist k t final)
    (keep : Preserved r n free pre t) (header : HeaderPreserved base t) (result : Result packet D q hist t final) :
    ∃ z : State ℚ, SafeRun (program batch) o (RowRAM.Within W) ⟨base.atPC 0,hist⟩ (k+3) ⟨z,final⟩ ∧
      z.output=some (if z.index 139=0 then 0 else 1) ∧
      Preserved r n free pre z.memory ∧ HeaderPreserved base z.memory ∧ Result packet D q hist z.memory final := by
  let u := LabelControl.marker t
  let pc := (LabelControl.ready (segment batch)).size+1+LabelControl.tag t
  let z : State ℚ := {u.atPC pc with output := some (LabelControl.tag t)}
  have safe : RowRAM.Within W u := run.finish
  refine ⟨z,LabelControl.taggedProgram_run run safe,?_,keep.marker,?_,result.marker⟩
  · simp [z,u,LabelControl.tag,LabelControl.marker,Memory.atPC]
  · intro j hj hi h₁ h₂ h₃
    simpa [z,u,State.memory,Memory.atPC,LabelControl.marker,show j≠6 by omega] using header j hj hi h₁ h₂ h₃

end LabelRAM
end Geometry
end LinearProgramming
end Optimization
end OAI

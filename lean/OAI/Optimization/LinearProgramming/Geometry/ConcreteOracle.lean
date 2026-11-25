import OAI.Optimization.LinearProgramming.Geometry.OracleAssembly
import OAI.Optimization.LinearProgramming.Geometry.LabelProcedureCode
import OAI.Optimization.LinearProgramming.Geometry.BorderBatchRAM
import OAI.Optimization.LinearProgramming.Geometry.LabelBatchInputs
import OAI.Optimization.LinearProgramming.Geometry.RawLabelInput

/-! One uniform scalar-oracle RAM for a designated geometric label, both as a callable
subroutine and from the bare dimensions, matrix entries, prices and designated coordinate. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM RAM.Block Contract OracleSegments Matrix

variable {r s n : ℕ}

/-- The normal entry loads dimensions and allocates its buffers before running the same
callable procedure, then returns its result or restart tag. -/
def geometricLabelEntry : Segment := .seq (.core LabelInput.rawHeader) geometricLabelProcedure

def geometricLabelProgram : OracleProgram := LabelControl.taggedProgram geometricLabelEntry

def geometricLabelWidth (r n e g H : ℕ) : ℕ :=
  LabelRAM.width r n (BorderBatch.batchLocalWidth n e g) (BorderBatch.batchIncrement n e g) H

def geometricLabelTime (r s n : ℕ) : ℕ := 10000*(r+s+n+1)^3+LabelRAM.time r n (BorderBatch.batchTime r n)

/-- The actual linked degree-dependent computation at the caller's supplied buffer
addresses. Its physical query instruction sends the canonical nonzero minor words. -/
theorem geometricLabelProcedure_run (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (q : PriceGame.Query n) (o : ScalarOracle ℚ) (base : Memory ℚ) (before : Contract.History ℚ)
    (x : LabelInput.Buffers r s n) (hdr : LabelInput.Header x D E q.prices q.index base)
    (e g H : ℕ) (hD : LinearIndependent ℚ D.row) (hrn : r≤n) (safe : RowRAM.Within H base)
    (hmat : ∀ i j, ratBits (D i j) ≤ e) (hprice : ∀ j, ratBits (q.prices j) ≤ e)
    (service : BorderBatch.Responds D E (fun v => ratBits v ≤ g) o) :
    ∃ t final k, k+3 ≤ LabelRAM.time r n (BorderBatch.batchTime r n) ∧
      Runs geometricLabelProcedure o (RowRAM.Within (geometricLabelWidth r n e g H)) base before k t final ∧
      (∀ a, 64≤a → a<x.layout.triples → t.data a=base.data a) ∧ LabelRAM.HeaderPreserved base t ∧
      LabelRAM.Result (BorderBatch.keyPacket D E) D q before t final ∧
      LabelRAM.Split BorderBatch.batchProgram o (RowRAM.Within (geometricLabelWidth r n e g H)) base before k t final := by
  have post : PostPivotLayout.Inputs r (base.index 134) x.layout.scratch q.index base :=
    hdr.batch.roundedAddr.symm ▸ hdr.post
  have capacity : base.index 134+r*n≤x.layout.scratch := hdr.batch.roundedAddr.symm ▸ x.rounded_end_le_scratch
  obtain ⟨t,final,k,hk,run,⟨u,kept,frame⟩,header,result,splitRun⟩ := LabelRAM.segment_run
    BorderBatch.batchProgram o (BorderBatch.keyPacket D E) D q base before (fun m _ => BorderBatch.PreservesInput x.layout base m)
    (BorderBatch.batchLocalWidth n e g) (BorderBatch.batchIncrement n e g) (BorderBatch.batchTime r n) H x.layout.scratch
    hdr.prefix hD post capacity safe hdr.border.aux_stable (fun _ _ _ => rfl)
    (BorderBatch.batch_sound D E q.prices base e g o hdr.border hD hrn hmat hprice service)
  refine ⟨t,final,k,hk,run,?_,header,result,splitRun⟩
  intro a ha hb
  have h₁ := x.layout.triples_end
  have h₂ := x.rounded_end_le_scratch
  have hs : a<x.layout.scratch := by omega
  exact (frame.data a ha (.inl hs)).trans (kept a (by omega) hb)

/-- The fixed bytecode needs no advice about bases, pivots, minor answers, projections,
or iteration counts. Its output includes the whole actual scalar query history. -/
theorem geometricLabelProgram_run (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (q : PriceGame.Query n) (o : ScalarOracle ℚ) (e g : ℕ) (hD : LinearIndependent ℚ D.row) (hrn : r≤n)
    (hd : ∀ i j, ratBits (D i j) ≤ e) (he : ∀ i j, ratBits (E i j) ≤ e)
    (hp : ∀ j, ratBits (q.prices j) ≤ e) (service : BorderBatch.Responds D E (fun v => ratBits v ≤ g) o) :
    ∃ k final, ∃ z : State ℚ, k≤geometricLabelTime r s n ∧
      SafeRun geometricLabelProgram o (RowRAM.Within (geometricLabelWidth r n e g (e+3)))
        ⟨start [r,s,n,q.index.val] (LabelInput.rawTape D E q.prices),[]⟩ k ⟨z,final⟩ ∧
      z.output=some (if z.index 139=0 then 0 else 1) ∧
      LabelRAM.Result (BorderBatch.keyPacket D E) D q [] z.memory final := by
  let H := e+3
  let W := geometricLabelWidth r n e g H
  let x := LabelInput.standardBuffers r s n
  let initial := start [r,s,n,q.index.val] (LabelInput.rawTape D E q.prices)
  have h₀ : ratBits (0 : ℚ)≤H := (show ratBits (0 : ℚ)≤3 by decide).trans (by dsimp [H]; omega)
  have heH : e≤H := by dsimp [H]; omega
  obtain ⟨m,c,hc,raw,header,_⟩ := LabelInput.rawHeader_spec (fun v : ℚ => ratBits v≤H) h₀ D E q.prices q.index
    (fun a b => (hd a b).trans heH) (fun a b => (he a b).trans heH) (fun j => (hp j).trans heH)
  obtain ⟨t,final,l,hl,body,_,_,result,_⟩ := geometricLabelProcedure_run D E q o m [] x header e g H hD hrn
    raw.safe_end hd hp service
  have inc : H≤W := (Nat.le_add_right H _).trans (le_max_left _ _)
  have setup : Runs (.core LabelInput.rawHeader) o (RowRAM.Within W) initial.memory [] c m [] :=
    (Runs.core raw o []).weaken fun _ z j => (z j).trans inc
  have both : Runs geometricLabelEntry o (RowRAM.Within W) initial.memory [] (c+l) t final := setup.seq body
  let u := LabelControl.marker t
  let pc := (LabelControl.ready geometricLabelEntry).size+1+LabelControl.tag t
  let z := {u.atPC pc with output := some (LabelControl.tag t)}
  have hmark : RowRAM.Within W u := both.finish
  refine ⟨c+l+3,final,z,by unfold geometricLabelTime; omega,LabelControl.taggedProgram_run both hmark,?_,result.marker⟩
  simp [z,u,LabelControl.tag,LabelControl.marker,Memory.atPC]

end Geometry
end LinearProgramming
end Optimization
end OAI

import OAI.ThreeFlat.Diagonal.PhysicalStageProgram
import OAI.ThreeFlat.Diagonal.ShrinkStageNav
import OAI.ThreeFlat.Diagonal.ShrinkTableOrdinal
import OAI.ThreeFlat.Diagonal.CompressorNodeRecipe
import OAI.ThreeFlat.Diagonal.RefreshKernelRecords
import OAI.ThreeFlat.Diagonal.RefreshNodeOwners
import OAI.ThreeFlat.Diagonal.HistogramAdmission
import OAI.ThreeFlat.RAM.TickStageSpec
import OAI.ThreeFlat.RAM.NextStage

namespace OAI
/-! # The actual trivalent compressor's fixed shrink and refresh native procedures -/

namespace ThreeFlat.Diagonal.NavigationPass

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.ContinuationLink
open CompressorPacking CompressorPacking.Native
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {W : ℕ}

def admit (current : Word W) (K : ℕ) : Procedure W :=
  ⟨_,_,0,AdmissionBank.block current.val K,Fin.elim0⟩

/-- The installed row loop on the true dense words is the tensor rewrite's record
parser, including on bad sums or nonzero trailing alphabet fields. -/
theorem admit_record (field : FieldCode F W) (width : 0<W) (current : Word W)
    {K count rows : ℕ} (R : HistogramRegister.Rows rows K W)
    (order : Fin count ≃ HistogramRegister.Choices R) (x : HistogramRegister.Words rows K W) :
    TickStageSpec.Admission field (admit current K).block (admit current K).publicData
      (fun m => AdmissionBank.Fits current.val K m ∧ HistogramRegister.BankLayout current.val R x m)
      (fun _=>((HistogramRegister.record R order).read (List.ofFn (HistogramRegister.bitTable x))).isSome)
      (fun m out=>out=m) (6+rows*(2*AdmissionBank.cost 0 K+4)) := by
  intro p r k M pc reg pub exit installed words c m start data
  obtain ⟨fits,loaded⟩ := data
  have equiv : ((HistogramRegister.record R order).read (List.ofFn (HistogramRegister.bitTable x))).isSome ↔
      HistogramRegister.admitted R x := by
    simp [HistogramRegister.record]
    change (if h : HistogramRegister.admitted R x then
      some (order.symm (HistogramRegister.choices R x h)) else none).isSome = true ↔ HistogramRegister.admitted R x
    by_cases h : HistogramRegister.admitted R x <;> simp [h]
  have rowsOk := HistogramRegister.valid_rows_iff_admitted loaded
  constructor
  · intro read
    obtain ⟨t,ht,d,run,out,_⟩ := AdmissionBank.advance_block current.val K width pc reg pub exit M
      installed c m start fits
    rw [ite_eq_left (rowsOk.mpr (equiv.mp read))] at out
    rw [loaded.count,AdmissionBank.cost_eq] at ht
    exact ⟨t,ht,d,m,out,rfl,run⟩
  · intro bad extra
    have rejected := AdmissionBank.reject_mass field current.val K width pc reg pub exit M installed
      c m start fits (fun ok=> bad (equiv.mpr (rowsOk.mp ok))) extra
    simpa only [loaded.count] using rejected

def scan (current : Word W) (p : ShrinkStage.Pass W) : Procedure W :=
  ⟨p.labels,p.regs,1,p.bank current,fun _ => 0⟩

def shrink (current : Word W) (K s D : ℕ) (T : ShrinkMotif.Table F) : Procedure W :=
  let d := 2^s
  let c := 2*d+1
  let count := PhysicalShrink.parallel c d D
  let S : Graph.Stage := ⟨d,c,count,∑ i,count i,usedDegree count c d,D⟩
  let row := T.row
  let size := fun i => Fintype.card (T.block (row i)).Alphabet
  let bits := fun i => (T.block (row i)).bits
  let table := fun i (j : Fin (size i)) e => (T.block (row i)).output ((Fintype.equivFin _).symm j) e
  (scan current (ShrinkStage.pre current S (CompressorPacking.tagBits d))).seq
    ((ShrinkStageNav.prepare current (T.base ∘ row) size).seq
      ((admit current K).seq ((ShrinkStageNav.commit current K size bits table).seq
        ((scan current ((ShrinkStage.NodeRecipe.after S K 1).install current)).seq (NextStage.procedure current)))))

def refresh (current : Word W) (K s h pad : ℕ) {c : Fin (2^s) → Fin (2^s) → ℕ} {C : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (sym : ∀ i j,c i j=c j i)
    (rows : ∀ i,∑ j,c i j=h) (loopless : ∀ i,c i i=0) : Procedure W :=
  let size := fun i => Fintype.card (T.block i).Alphabet
  let bits := fun i => (T.block i).bits
  let number := DoublePorts.arcNumber (Equiv.refl _) c rows
  let table := fun i (j : Fin (size i)) a b =>
    (T.block i).output ((Fintype.equivFin _).symm j) (number.symm (a,b))
  let E := DoublePorts.ofMatrix (Equiv.refl _) c sym rows loopless
  (RefreshStageNav.prepare current T.base size).seq
    ((admit current K).seq ((RefreshStageNav.commit current E pad K T.base size bits table).seq
      ((RefreshStageNav.Records.pipeline current (2^s) (1+h+pad) K).program.seq
       ((RefreshNodeOwners.procedure current (2^s)).seq (NextStage.procedure current)))))


end
end ThreeFlat.Diagonal.NavigationPass

end OAI

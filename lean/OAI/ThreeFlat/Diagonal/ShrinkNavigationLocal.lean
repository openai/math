import OAI.ThreeFlat.Diagonal.ShrinkNavigationExecution
import OAI.ThreeFlat.RAM.AdmissionSandwich

namespace OAI
/-! # The conditional histogram branch of the actual native shrinking stage -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure
open CompressorPacking CompressorPacking.Native
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {w : ℕ}

def shrinkStage (s D : ℕ) : Graph.Stage :=
  let d:=2^s
  let c:=2*d+1
  let count:=PhysicalShrink.parallel c d D
  ⟨d,c,count,∑ i,count i,usedDegree count c d,D⟩

def shrinkOld (current : Word w) (s D : ℕ) : Execution w :=
  Execution.pass current (ShrinkStage.pre current (shrinkStage s D) (tagBits (2^s)))

def shrinkChoices (current : Word w) (T : ShrinkMotif.Table F) : Execution w :=
  let size := fun i=>Fintype.card (T.block (T.row i)).Alphabet
  Execution.header current 2 28 (ShrinkStageNav.choiceWords current (T.base ∘ T.row) size)

def shrinkPublish (current : Word w) (K s D : ℕ) (T : ShrinkMotif.Table F) : Execution w :=
  let size := fun i=>Fintype.card (T.block (T.row i)).Alphabet
  let bits := fun i=>(T.block (T.row i)).bits
  let table := fun i (j : Fin (size i)) e=>(T.block (T.row i)).output ((Fintype.equivFin _).symm j) e
  let issued := Execution.header current 3 29 (ShrinkStageNav.widthWords current K size bits table)
  let «prefix» := Execution.header current 30 31 (ShrinkStageNav.prefixWords current)
  let decision := Execution.header current 32 33 (ShrinkStageNav.layoutWord current)
  let graph := Execution.pass current ((ShrinkStage.NodeRecipe.after (shrinkStage s D) K 1).install current)
  (issued.seq («prefix».seq decision)).seq (graph.seq (Execution.next current))

theorem shrink_code (current : Word w) (K s D : ℕ) (T : ShrinkMotif.Table F) :
    shrink current K s D T = (shrinkOld current s D).code.seq
      ((shrinkChoices current T).code.seq ((admit current K).seq (shrinkPublish current K s D T).code)) := rfl

/-- No validity hypothesis is imposed on `raw`. All words up to the guard are
produced by the real stage sweeps. The only suffix fit required is on an
accepted record; rejection has zero weight for every following continuation. -/
theorem shrink_native (field : FieldCode F w) (width : 0<w) (current : Word w)
    (K s D : ℕ) (T : ShrinkMotif.Table F) {count rows : ℕ}
    (R : HistogramRegister.Rows rows K w) (order : Fin count ≃ HistogramRegister.Choices R)
    (raw : HistogramRegister.Words rows K w) (input : Memory w) (postCost : ℕ)
    (oldFits : (shrinkOld current s D).fits input)
    (prepareFits : (shrinkChoices current T).fits ((shrinkOld current s D).run input).2)
    (ready : let m:=((shrinkChoices current T).run ((shrinkOld current s D).run input).2).2
      AdmissionBank.Fits current.val K m ∧ HistogramRegister.BankLayout current.val R raw m)
    (publish : let m:=((shrinkChoices current T).run ((shrinkOld current s D).run input).2).2
      ((HistogramRegister.record R order).read (List.ofFn (HistogramRegister.bitTable raw))).isSome →
      (shrinkPublish current K s D T).fits m ∧ ((shrinkPublish current K s D T).run m).1≤postCost) :
    let A:=shrinkOld current s D
    let B:=shrinkChoices current T
    let C:=shrinkPublish current K s D T
    let u:=A.run input
    let v:=B.run u.2
    TickStageSpec.Admission field (shrink current K s D T).block (shrink current K s D T).publicData
      (fun m=>m=input)
      (fun _=>((HistogramRegister.record R order).read (List.ofFn (HistogramRegister.bitTable raw))).isSome)
      (fun _ out=>out=(C.run v.2).2) (u.1+(v.1+((6+rows*(2*AdmissionBank.cost 0 K+4))+postCost))) := by
  let A:=shrinkOld current s D
  let B:=shrinkChoices current T
  let C:=shrinkPublish current K s D T
  let u:=A.run input
  let v:=B.run u.2
  let yes:Prop:=((HistogramRegister.record R order).read (List.ofFn (HistogramRegister.bitTable raw))).isSome
  let guard := admit current K
  let guardCost := 6+rows*(2*AdmissionBank.cost 0 K+4)
  have bank : TickStageSpec.Admission field guard.block guard.publicData
      (fun m=>m=v.2) (fun _=>yes) (fun a b=>b=a) guardCost :=
    TickStageSpec.Admission.mono (admit_record field width current R order raw)
      (by rintro m rfl; exact ready) (fun _ _=>Iff.rfl) (fun _ _ _ _ h=>h) le_rfl
  have later : C.code.Spec (fun m=>m=v.2 ∧ yes) (fun _ out=>out=(C.run v.2).2) postCost := by
    intro n r k M pc reg pub exit inst words cfg m entry ok
    obtain ⟨same,valid⟩:=ok
    obtain ⟨fit,time⟩:=publish valid
    subst m
    obtain ⟨ticks,bound,last,out,run,returned,correct⟩ :=
      C.correct v.2 fit M pc reg pub exit inst words cfg _ entry rfl
    exact ⟨ticks,bound.trans time,last,out,run,returned,correct⟩
  let tail := B.code.seq (guard.seq C.code)
  have middle : TickStageSpec.Admission field tail.block tail.publicData
      (fun m=>m=u.2) (fun _=>yes) (fun _ out=>out=(C.run v.2).2) (v.1+(guardCost+postCost)) :=
    TickStageSpec.guarded field B.code guard C.code
      (fun m=>m=u.2) (fun m=>m=v.2) yes (fun _=>v.2) (fun _=>(C.run v.2).2) _ _ _
      (B.correct u.2 prepareFits) (fun _ _=>rfl) bank later
  change TickStageSpec.Admission field (shrink current K s D T).block (shrink current K s D T).publicData
    (fun m=>m=input) (fun _=>yes) (fun _ out=>out=(C.run v.2).2) (u.1+(v.1+(guardCost+postCost)))
  rw [shrink_code]
  intro labels registers slots M
  exact TickStageSpec.Admission.mono
    (TickStageSpec.admission_seq field A.code tail (good:=fun _=>yes)
      (TickStageSpec.admission_of_spec field A.code (A.correct input oldFits)) middle
      (fun _ _ _=>trivial) (fun _ _ _ _ h=>⟨h,Iff.rfl⟩))
    (fun _ h=>h) (fun _ _=>Iff.rfl) (fun _ _ _ _ h=>h.choose_spec.2) le_rfl M

end
end ThreeFlat.Diagonal.NavigationPass

end OAI

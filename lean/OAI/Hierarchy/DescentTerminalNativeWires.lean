import OAI.Hierarchy.DescentTerminalRAMTrace
import OAI.Hierarchy.TaggedWideObservedBits

namespace OAI
/-! # Static initial-header wires and uniquely decoded terminal RAM workspace -/

namespace Hierarchy.DescentTerminalRAM
open ThreeFlat Routing SortNetwork Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open Tagged Tagged.SortLift TerminalSort DescentTerminalHost.SortBank
open TaggedShorterChronology TaggedShorterHistoryOrder TaggedShorterControlHistory
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {E B : Type} [Fintype E] [Fintype B] {w p r k f S u m n steps : ℕ}

abbrev Observed (u w : ℕ) := Fin u×Fin (w+1)
abbrev Workspace (B : Type) (w r f u m steps : ℕ) :=
  B ⊕ (TaggedShorterClock.Pin w r f ⊕ (Observed u w ⊕ TracePin m w steps))

def publicChoice : E ⊕ B→E ⊕ Workspace B w r f u m steps := Sum.map id Sum.inl

def traceInput (i : TracePin m w steps) : E ⊕ Workspace B w r f u m steps :=
  .inr (.inr (.inr (.inr i)))

def dataInput : (E ⊕ B) ⊕ Observed u w → E ⊕ Workspace B w r f u m steps :=
  Sum.elim publicChoice (fun i=>.inr (.inr (.inr (.inl i))))

def programInput (init : Fin S×Fin (w+1)→(E ⊕ B) ⊕ Bool) :
    Pins S f u w r m→(E ⊕ Workspace B w r f u m steps) ⊕ Bool
  | .inl (.inl i)=>(init i).map publicChoice id
  | .inl (.inr (.inl i))=>.inl (.inr (.inr (.inl i)))
  | .inl (.inr (.inr i))=>.inl (.inr (.inr (.inr (.inl i))))
  | .inr (.inl j)=>.inl (traceInput (0,j))
  | .inr (.inr j)=>.inl (traceInput (Fin.last steps,j))

def buffers (t : Fin (steps+1)) : RowRead (2^m) (RecordWidth (w+1)) (E ⊕ Workspace B w r f u m steps) :=
  fun j k=>.inl (traceInput (t,j,k))

def frameData : (TracePin m w steps→Bool) ≃ Frames m w steps :=
  (Equiv.curry _ _ _).trans (Equiv.piCongrRight fun _=>Equiv.curry _ _ _)

abbrev View (B : Type) (w r f u m steps : ℕ) :=
  (B→Bool)×((TaggedShorterClock.Pin w r f→Bool)×((Fin u→Word (w+1))×Frames m w steps))

def view : (Workspace B w r f u m steps→Bool) ≃ View B w r f u m steps :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        (Equiv.prodCongr (observationBits u (w+1)).symm frameData)))))

def workspace (b : B→Bool) (raw : TaggedShorterClock.Pin w r f→Bool) (obs : Fin u→Word (w+1))
    (record : Frames m w steps) : Workspace B w r f u m steps→Bool := view.symm (b,raw,obs,record)

omit [Fintype B] in
@[simp] theorem workspace_choice (b : B→Bool) (raw : TaggedShorterClock.Pin w r f→Bool) (obs : Fin u→Word (w+1))
    (record : Frames m w steps) (i : B) : workspace b raw obs record (.inl i)=b i := rfl

omit [Fintype E] [Fintype B] in
theorem program_read (init : Fin S×Fin (w+1)→(E ⊕ B) ⊕ Bool) (x : E→Bool) (b : B→Bool)
    (base : ℕ→Word w) (h0 : ∀i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base i.1.val)) i.2)
    (raw : TaggedShorterClock.Pin w r f→Bool) (obs : Fin u→Word (w+1)) (record : Frames m w steps) :
    Sum.elim (Sum.elim x (workspace b raw obs record)) id ∘ programInput init=
      Sum.elim (controls (wide ∘ base) raw obs) (Sum.elim (Function.uncurry (record 0))
        (Function.uncurry (record (Fin.last steps)))) := by
  funext i
  rcases i with ((p|(p|p))|(p|p))
  · have atPin:=h0 p
    cases eq : init p with
    | inl u=>cases u <;> simpa [eq,programInput,publicChoice,controls,Function.comp_apply] using atPin
    | inr val=>simpa [eq,programInput,controls,Function.comp_apply] using atPin
  all_goals rfl

omit [Fintype E] [Fintype B] in
theorem data_read (x : E→Bool) (b : B→Bool) (raw : TaggedShorterClock.Pin w r f→Bool)
    (obs : Fin u→Word (w+1)) (record : Frames m w steps) :
    Sum.elim x (workspace b raw obs record) ∘ dataInput =
      Sum.elim (Sum.elim x b) (observationBits u (w+1) obs) := by
  funext q
  rcases q with (q|q)|q <;> rfl

omit [Fintype E] [Fintype B] in
theorem buffers_read (stages : Fin steps→Stage (2^m)) (small : ∀i b,(stages i).length b≤2^n)
    (x : E→Bool) (b : B→Bool) (raw : TaggedShorterClock.Pin w r f→Bool) (obs : Fin u→Word (w+1))
    (record : Frames m w steps) :
    Accepts id (traceRead (n:=n) stages id buffers) (Sum.elim x (workspace b raw obs record)) ↔
    Pass (n:=n) stages record := by
  rw [trace_iff stages id small buffers,pass_steps stages small]
  rfl

theorem workspace_size (B : Type) [Fintype B] (w r f u m steps : ℕ) :
    Fintype.card (Workspace B w r f u m steps) =
      Fintype.card B+f*((5+r)*(w+1))+u*(w+1)+(steps+1)*(2^m*RecordWidth (w+1)) := by
  simp only [Workspace,TaggedShorterClock.Pin,Observed,TracePin,Bus,TaggedShorterChronoArray.Output,
    Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

end
end Hierarchy.DescentTerminalRAM

end OAI

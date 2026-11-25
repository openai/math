import OAI.Hierarchy.DescentTerminalStageSort
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Flattening all local comparisons in a staged terminal sort into one bank -/

namespace Hierarchy.DescentTerminalHost.SortBank
open Tagged Tagged.TerminalSort Tagged.SortLift
open scoped BigOperators Classical
noncomputable section

variable {n l steps d w : ℕ} {V : Type}
variable (stages : Fin steps→Stage l) (digit : Fin d→Fin w)

def localCount := ∑ t,(stages t).blocks

def index : ((t : Fin steps) × Fin (stages t).blocks) ≃ Fin (localCount stages) := finSigmaFinEquiv

def traceRead (readRow : Fin (steps+1)→RowRead l w V) :
    BatchRead n w (localCount stages) V := fun j=>
  let u := (index stages).symm j
  stageRead (stages u.1) digit (readRow u.1.castSucc) (readRow u.1.succ) u.2

theorem trace_iff (room : ∀i b,(stages i).length b≤2^n) (readRow : Fin (steps+1)→RowRead l w V) (v : V→Bool) :
    Accepts digit (traceRead (n:=n) stages digit readRow) v ↔
      ∀t,rowValue v (readRow t.succ)=(stages t).eval (key digit) (rowValue v (readRow t.castSucc)) := by
  let passes (r : SortRelation.Ends n w → V ⊕ Bool) : Prop :=
    output (fun _ : Fin 1 => r) v 0 =
      ThreeFlat.Routing.SortNetwork.pack
        (sorted digit (inside (fun _ : Fin 1 => r) v 0))
  have readAt (u : (t : Fin steps) × Fin (stages t).blocks) :
      traceRead (n:=n) stages digit readRow (index stages u) =
        stageRead (stages u.1) digit (readRow u.1.castSucc) (readRow u.1.succ) u.2 :=
    congrArg (fun b : (t : Fin steps) × Fin (stages t).blocks =>
      stageRead (n:=n) (stages b.1) digit (readRow b.1.castSucc) (readRow b.1.succ) b.2)
      ((index stages).symm_apply_apply u)
  constructor
  · intro all t
    apply (stage_iff (stages t) digit (room t) _ _ v).mp
    intro b
    exact (congrArg passes (readAt ⟨t,b⟩)).mp (all (index stages ⟨t,b⟩))
  · intro all j
    obtain ⟨⟨t,b⟩,rfl⟩:=(index stages).surjective j
    have pass:=(stage_iff (stages t) digit (room t) _ _ v).mpr (all t)
    exact (congrArg passes (readAt ⟨t,b⟩)).mpr (pass b)

/-- Correctly executed successive layers determine the final array. -/
theorem last_of_steps {α κ : Type*} [LinearOrder κ] (key : α→κ)
    (r : Fin (steps+1)→Fin l→α) (step : ∀i,r i.succ=(stages i).eval key (r i.castSucc)) :
    r (Fin.last steps)=SortLift.run (List.ofFn stages) key (r 0) := by
  induction steps with
  | zero => simp [SortLift.run]
  | succ z ih =>
    have tail:=ih (fun i : Fin z=>stages i.succ) (fun t : Fin (z+1)=>r t.succ)
      (fun i=>step i.succ)
    have first : (stages 0).eval key (r 0)=r (Fin.succ 0) := (step 0).symm
    simpa only [List.ofFn_succ,SortLift.run,List.foldl_cons,Fin.succ_last,
      first] using tail

theorem run_readback (room : ∀i b,(stages i).length b≤2^n) (readRow : Fin (steps+1)→RowRead l w V)
    (v : V→Bool) (ok : Accepts digit (traceRead (n:=n) stages digit readRow) v) :
    rowValue v (readRow (Fin.last steps))=
      SortLift.run (List.ofFn stages) (key digit) (rowValue v (readRow 0)) :=
  last_of_steps stages (key digit) (fun i=>rowValue v (readRow i))
    ((trace_iff stages digit room readRow v).mp ok)

/-- Fixed exposed initial data has exactly one full sequence of arrays
that passes every physical layer. The proof constructs it forward. -/
theorem exists_unique_trace {α κ : Type*} [LinearOrder κ] (key : α→κ) (x : Fin l→α) :
    ∃! r : Fin (steps+1)→Fin l→α, r 0=x ∧ ∀t,r t.succ=(stages t).eval key (r t.castSucc) := by
  let build (t : Fin (steps+1)) : Fin l→α := Fin.induction x (fun i a=>(stages i).eval key a) t
  have first : build 0=x := rfl
  have step (i : Fin steps) : build i.succ=(stages i).eval key (build i.castSucc) := by
    simp [build]
  refine ⟨build,⟨first,step⟩,?_⟩
  intro r hr
  funext t
  induction t using Fin.induction with
  | zero => exact hr.1.trans first.symm
  | succ i ih => rw [hr.2 i,step i,ih]

end
end Hierarchy.DescentTerminalHost.SortBank

end OAI

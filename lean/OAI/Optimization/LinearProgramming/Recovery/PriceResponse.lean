import OAI.Optimization.LinearProgramming.Recovery.PriceHandler
import OAI.Optimization.LinearProgramming.Geometry.PriceStepRAM

/-! The native packet handler agrees with the deterministic price service computed
from the saved chronological minor transcript. This identifies individual executions,
including the returned numerical cache after the first interrupted minor. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

open RAM RAM.Callable Contract OracleSpec BitRAM Geometry
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Recovery.OracleInline

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

def Stored (S : Service D E) (x : LabelInput.Buffers r s n) (hist : History ℚ) (H : ℕ) (a : Memory ℚ) : Prop :=
  ∃ minor g,a=Odd.memory minor g ∧ cache S hist minor ∧ PriceLayout.Matrices x D E g ∧
    RowRAM.Within H g ∧ answersMatch S.oracle hist

def preservedPorts (m v : Memory ℚ) : Prop := v.index sendBaseReg=m.index sendBaseReg ∧
  ∀ j,50 ≤ j → j < 65 → v.index j=m.index j

def Response (p : BitProgram) (c : p.Config) (q : Fin p.states) (m v : Memory ℚ) : Option Bool→Prop
  | none => v.index nilReg=0 ∧ v.index statusReg=1 ∧ preservedPorts m v
  | some b => HeapRep p (contents c) v ∧ v.index stateReg=q.val ∧ v.index statusReg=0 ∧
    v.index recvBaseReg=3 ∧ v.index recvLenReg=1 ∧ ScalarPacket v 3 [b] ∧ preservedPorts m v

private theorem clean_label {packet : PivotKey n→List ℚ} {q : PriceGame.Query n} {old final : History ℚ}
    {g : Memory ℚ} (result : LabelRAM.Result packet D q old g final) (normal : g.index 139=0) :
    g.data 19=bitScalar (decide (g.data 19=1)) := by
  cases result with
  | completed _ _ _ _ _ value => split at value <;> simp [value,bitScalar]
  | restarted _ _ _ _ _ => omega

private theorem savedIndex {K : Type*} (v t : Memory K) (x : K) {j : ℕ}
    (frame : ∀a,5 ≤ a→t.index a=v.index a) (hj : 31 ≤ j) (hb : j≠recvBaseReg)
    (hl : j≠recvLenReg) (hf : j≠statusReg) :
    (answerMemory (t.putIndex 1 0) x).index j=v.index j := by
  have h0 : j≠0 := by omega
  have h1 : j≠1 := by omega
  simpa [answerMemory,Memory.putIndex,Function.update,Memory.putData,hb,hl,hf,h0,h1] using frame j (by omega)

private theorem recordResponse {p : BitProgram} {c : p.Config} {pc : Fin p.states}
    {vm g v : Memory ℚ} {q : PriceGame.Query n} {old final : History ℚ}
    (wait : Awaiting p c pc vm) (clean : vm.index statusReg=0) (returned : Returned vm g v)
    (S : Service D E) (result : LabelRAM.Result (keyPacket D E) D q old g final)
    (legal : answersMatch S.oracle final) : Response p c pc vm v (S.priceStep old q).1 ∧ (S.priceStep old q).2=final := by
  rw [result.priceStep_eq S legal]
  cases returned with
  | restart temp indices flag =>
    simp only [flag,show (1:ℕ)≠0 by decide,ite_false,Response,and_true]
    refine ⟨?_,rfl,?_,?_⟩
    · change temp.index nilReg=0
      exact (indices nilReg (by decide)).trans wait.heap.nilValue
    · change temp.index sendBaseReg=vm.index sendBaseReg
      exact indices _ (by decide)
    · intro j lo _
      have h0 : j≠0 := by omega
      have h1 : j≠1 := by omega
      have h45 : j≠statusReg := by unfold statusReg; omega
      simpa [restartMemory,Memory.putIndex,Function.update,h0,h1,h45] using indices j (by omega)
  | answer temp indices flag =>
    simp only [flag,ite_true,and_true,Response]
    let v:=answerMemory (temp.putIndex 1 0) (g.data 19)
    have frame (i : ℕ) (lo : 31 ≤ i) (hb : i≠recvBaseReg) (hl : i≠recvLenReg) : v.index i=vm.index i := by
      by_cases hf : i=statusReg
      · subst i; change 0=vm.index statusReg; exact clean.symm
      · exact savedIndex vm temp _ indices lo hb hl hf
    refine ⟨NativeService.heap_of_frame (fun i lo _ hb hl=>frame i lo hb hl) wait.heap,
      (frame stateReg (by decide) (by decide) (by decide)).trans wait.stateCode,rfl,rfl,rfl,?_,⟨frame sendBaseReg (by decide) (by decide) (by decide),fun j lo _=>frame j (by omega) (by unfold recvBaseReg;omega) (by unfold recvLenReg;omega)⟩⟩
    let b:=decide (g.data 19=1)
    have value : g.data 19=bitScalar b:=clean_label result flag
    change ScalarPacket (answerMemory (temp.putIndex 1 0) (g.data 19)) 3 [b]
    rw [congrArg (answerMemory (temp.putIndex 1 0)) value]
    exact answer_packet _ b

theorem handler_at_price (S : Service D E) (x : LabelInput.Buffers r s n) (q : PriceGame.Query n)
    (old : History ℚ) {p : BitProgram} {c : p.Config} {pc : Fin p.states} (native vm : Memory ℚ)
    (wait : Awaiting p c pc vm) (clean : vm.index statusReg=0) (word : ScalarPacket vm (vm.index 43) (priceQuery q.index q.prices))
    (len : vm.index 37=(priceQuery q.index q.prices).length) (send : 3 ≤ vm.index 43)
    (room : 256+(priceQuery q.index q.prices).length ≤ x.dual)
    (H e W : ℕ) (stored : Stored S x old H native) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n)
    (vmSafe : vm.AllData (fun z=>ratBits z ≤ W)) (all : H+geometricIncrement r s n e S.outputBits ≤ W)
    (arg : (priceQuery q.index q.prices).length+3 ≤ H) (encoded : (priceQuery q.index q.prices).length+3 ≤ e)
    (matrix : ∀i j,ratBits (D i j) ≤ e) (height : S.height ≤ H) (ready : RowRAM.Within S.height S.ready.memory) :
    ∃ next v,(priceHandler S.program).Run (fun z=>ratBits z ≤ W) (Odd.memory native vm)
      (priceHandlerTime r s n S.clock (priceQuery q.index q.prices).length) (Odd.memory next v) ∧
      Stored S x (S.priceStep old q).2 (H+geometricIncrement r s n e S.outputBits) next ∧
      Response p c pc vm v (S.priceStep old q).1 := by
  obtain ⟨minor,g,rfl,trained,input,gs,admissible⟩:=stored
  obtain ⟨t,final,next,v,kept,matrices,ts,run,received,legal,result⟩:=priceHandler_run S x q old minor g vm input
    word len send room H e W hD hrn gs vmSafe all arg encoded matrix height ready trained
  have legalFinal:=legal admissible
  obtain ⟨ans,history⟩:=recordResponse wait clean received S result legalFinal
  exact ⟨Odd.memory next t,v,run,history.symm ▸ ⟨next,t,rfl,kept,matrices,ts,legalFinal⟩,ans⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI

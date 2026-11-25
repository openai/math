import OAI.Optimization.LinearProgramming.Recovery.PhysicalEpoch
import OAI.Optimization.LinearProgramming.Geometry.SealedSignRecovery

/-! A single finite physical loop across all genuine minor-service restarts. The
learner is reset after each interruption, while the whole numerical bank survives. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM RAM.Tape RAM.Callable OracleSpec Contract BitRAM Geometry
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Recovery.OracleInline

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

def retryGuard : Cond := Odd.cond (.addrLT nilReg statusReg)
private def arm : Block := .seq (.op (.addrConst nilReg 0)) (.op (.addrConst statusReg 1))

noncomputable def retry (p : BitProgram) (B : Polynomial ℕ) (minor : Program) : Fragment :=
  .seq (Odd.leaf arm) (.loop retryGuard (episode p B minor))

noncomputable def retryTime (p : BitProgram) (B : Polynomial ℕ) (r s n service T cap : ℕ) : ℕ :=
  8+((cap+1)*(episodeTime p B r s n service T+2)+1)

theorem physical_restart (S : Service D E) (x : LabelInput.Buffers r s n) (p : BitProgram) (B : Polynomial ℕ)
    (anchor : Fin n) (sign : Bool) (T e H inputBase W cap : ℕ) (native vm : Memory ℚ)
    (pcg : ∀ f : Transcript→Word→Bool,p.ComputesWithin (fun h w=>[f h w]) (priceInput (2^(1+B.eval n)) anchor) T
      (pricePost (2^(1+B.eval n)) anchor))
    (consistent : ∀ prior before,ServicePath S.serveWord [] prior before → ∀ev after,
      ServicePath S.serveWord before ev after → restartCount ev=0 →
      ∃ active : Set (Fin n),∃ costs : Fin n→ℕ,anchor∈active ∧ (∀j∈active,costs j ≤ 2^(1+B.eval n)) ∧
        priceConsistent sign active costs (BitEpoch.wordHistory ev))
    (bounded : ∀ ev after,ServicePath S.serveWord [] ev after → restartCount ev ≤ cap)
    (initial : Stored S x [] H native) (ports : Ports anchor inputBase vm) (space : 3 ≤ inputBase)
    (vmSafe : RowRAM.Within W vm) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n) (buffer : 256+T ≤ x.dual)
    (height : S.height ≤ H) (ready : RowRAM.Within S.height S.ready.memory)
    (arg : T+3 ≤ H) (encoded : T+3 ≤ e) (matrix : ∀i j,ratBits (D i j) ≤ e)
    (envelope : H+(cap+1)*((T+1)*geometricIncrement r s n e S.outputBits) ≤ W) :
    ∃ ev after next v,(retry p B S.program).Run (fun z=>ratBits z ≤ W) (Odd.memory native vm)
      (retryTime p B r s n S.clock T cap) (Odd.memory next v) ∧ ServicePath S.serveWord [] ev after ∧
      Stored S x after W next ∧ v.index statusReg=0 ∧ v.data (v.index sendBaseReg)=bitScalar sign := by
  let Δ:=(T+1)*geometricIncrement r s n e S.outputBits
  let cost:=episodeTime p B r s n S.clock T
  let body:=episode p B S.program
  let P:=fun z : ℚ=>ratBits z ≤ W
  have loop (left : ℕ) : ∀ prior before a m,ServicePath S.serveWord [] prior before → restartCount prior+left=cap →
      Stored S x before (H+restartCount prior*Δ) a → Ports anchor inputBase m → Good P m →
      m.index nilReg=0 → 0 < m.index statusReg → ∃ ev after next v,
      (Fragment.loop retryGuard body).Run P (Odd.memory a m) ((left+1)*(cost+2)+1) (Odd.memory next v) ∧
      ServicePath S.serveWord before ev after ∧ Stored S x after W next ∧ v.index statusReg=0 ∧
      v.data (v.index sendBaseReg)=bitScalar sign := by
    induction left using Nat.strong_induction_on with
    | h left ih =>
      intro prior before a m past room current portState ms nil0 flag
      have used:=bounded prior before past
      have oneMore:=Nat.mul_le_mul_right Δ (Nat.succ_le_succ used)
      rw [Nat.succ_mul] at oneMore
      have fit : H+restartCount prior*Δ+Δ ≤ W := by dsimp [Δ] at oneMore ⊢;omega
      have floor : H ≤ H+restartCount prior*Δ:=Nat.le_add_right _ _
      obtain ⟨ev,after,next,v,cut,run,path,count,_,trained,vports,ending⟩:=physical_epoch S x p B anchor sign before
        T e (H+restartCount prior*Δ) inputBase W a m pcg (consistent prior before past) current portState space ms hD hrn
        buffer (height.trans floor) ready (arg.trans floor) encoded matrix fit
      have test : retryGuard.test (Odd.memory a m)=true:=by
        unfold retryGuard
        rw [Odd.cond_test]
        simp [Cond.test,nil0,flag]
      cases ending with
      | complete zero normal answer =>
        have stop : retryGuard.test (Odd.memory next v)=false:=by
          unfold retryGuard
          rw [Odd.cond_test]
          simp [Cond.test,normal]
        have finished:=Fragment.Run.loopFalse (P := P) stop run.safe_end body
        have baseBound : cost+2 ≤ (left+1)*(cost+2) :=
          (Nat.one_mul (cost+2)).symm.le.trans
            (Nat.mul_le_mul_right (cost+2) (Nat.succ_le_succ (Nat.zero_le left)))
        refine ⟨ev,after,next,v,(Fragment.Run.loopTrue test run finished).mono ?_,path,trained.mono fit,normal,answer⟩
        change 1+cost+1+1 ≤ (left+1)*(cost+2)+1
        exact (show 1+cost+1+1 ≤ (cost+2)+1 by omega).trans (Nat.add_le_add_right baseBound 1)
      | interrupted zero positive =>
        have joined:=past.append path
        have count' : restartCount (prior++ev)=restartCount prior+1:=by rw [restartCount_append,count];rfl
        have capBound:=bounded (prior++ev) after joined
        rw [count'] at capBound
        let rem:=left-1
        have less : rem < left:=by dsimp [rem];omega
        have sum : restartCount (prior++ev)+rem=cap:=by rw [count'];dsimp [rem];omega
        have nextWidth : Stored S x after (H+restartCount (prior++ev)*Δ) next:=by
          rw [count',Nat.succ_mul,← Nat.add_assoc];exact trained
        have vs : Good P v:=fun j=>by simpa only [Odd.data_slot] using run.safe_end (Odd.slot j)
        obtain ⟨tail,last,b,w,rest,log,keep,normal,answer⟩:=ih rem less (prior++ev) after next v joined sum nextWidth vports vs zero positive
        refine ⟨ev++tail,last,b,w,(Fragment.Run.loopTrue test run rest).mono ?_,path.append log,keep,normal,answer⟩
        change 1+cost+1+((rem+1)*(cost+2)+1) ≤ (left+1)*(cost+2)+1
        have eq : left=rem+1:=by dsimp [rem];omega
        rw [eq,Nat.succ_mul (rem+1)];omega
  let a:=vm.putIndex nilReg 0
  let m:=a.putIndex statusReg 1
  have first:=Block.Eval.op_addrConst (safe:=Memory.AllData P) vm nilReg 0 vmSafe vmSafe
  have second:=Block.Eval.op_addrConst (safe:=Memory.AllData P) a statusReg 1 vmSafe vmSafe
  have armRun:=Odd.leaf_run P native (initial.safe height (by omega) ready) (first.seq second)
  have mports : Ports anchor inputBase m:=⟨ports.send,ports.columns,ports.index,ports.packet⟩
  obtain ⟨ev,after,next,v,rest,path,keep,normal,answer⟩:=loop cap [] [] native m (.nil _) (by simp) (by simpa using initial)
    mports vmSafe rfl (by decide : 0 < 1)
  exact ⟨ev,after,next,v,armRun.seq rest,path,keep,normal,answer⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI

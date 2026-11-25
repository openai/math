import OAI.Optimization.LinearProgramming.Recovery.EpochHandles
import OAI.Optimization.LinearProgramming.Recovery.OddEpochRun

/-! One entire real restarted trial up to a genuine service interruption or the
correct learned sign, including the typed input and the final physical scalar bit. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM RAM.Callable OracleSpec Contract BitRAM Geometry
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Recovery.OracleInline

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

def exposeWord : Fragment := .branch (Odd.cond (.addrLT nilReg statusReg)) (Odd.leaf .skip) (Odd.leaf preparePacket)

noncomputable def episode (p : BitProgram) (B : Polynomial ℕ) (minor : Program) : Fragment :=
  .seq (resetEpoch p B) (.seq (epochLoop p (priceHandler minor)) exposeWord)

noncomputable def episodeTime (p : BitProgram) (B : Polynomial ℕ) (r s n serviceBudget T : ℕ) : ℕ :=
  resetTime p B n+(epochUnit p (transferTime r s n serviceBudget T)*(T+1)+5+81)

inductive ResultWord (b : Bool) (v : Memory ℚ) : Bool→Prop where
  | complete (nil0 : v.index nilReg=0) (flag : v.index statusReg=0)
      (value : v.data (v.index sendBaseReg)=bitScalar b) : ResultWord b v false
  | interrupted (nil0 : v.index nilReg=0) (flag : 0 < v.index statusReg) : ResultWord b v true

theorem Stored.mono {S : Service D E} {x : LabelInput.Buffers r s n} {h : History ℚ} {H G : ℕ}
    {a : Memory ℚ} (stored : Stored S x h H a) (le : H ≤ G) : Stored S x h G a := by
  obtain ⟨m,t,rfl,trained,mat,good,history⟩:=stored
  exact ⟨m,t,rfl,trained,mat,fun j=>(good j).trans le,history⟩

theorem physical_epoch (S : Service D E) (x : LabelInput.Buffers r s n) (p : BitProgram) (B : Polynomial ℕ)
    (anchor : Fin n) (sign : Bool) (before : History ℚ) (T e baseWidth wordBase W : ℕ) (native vm : Memory ℚ)
    (pcg : ∀ f : Transcript→Word→Bool,p.ComputesWithin (fun h w=>[f h w]) (priceInput (2^(1+B.eval n)) anchor) T
      (pricePost (2^(1+B.eval n)) anchor))
    (consistent : ∀ ev after,ServicePath S.serveWord before ev after → restartCount ev=0 →
      ∃ active : Set (Fin n),∃ costs : Fin n→ℕ,anchor∈active ∧ (∀j∈active,costs j ≤ 2^(1+B.eval n)) ∧
        priceConsistent sign active costs (BitEpoch.wordHistory ev))
    (initial : Stored S x before baseWidth native) (ports : Ports anchor wordBase vm) (wordRoom : 3 ≤ wordBase)
    (vmSafe : RowRAM.Within W vm) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n) (room : 256+T ≤ x.dual)
    (height : S.height ≤ baseWidth) (ready : RowRAM.Within S.height S.ready.memory)
    (arg : T+3 ≤ baseWidth) (encoded : T+3 ≤ e) (matrix : ∀i j,ratBits (D i j) ≤ e)
    (envelope : baseWidth+(T+1)*geometricIncrement r s n e S.outputBits ≤ W) :
    let Δ:=geometricIncrement r s n e S.outputBits
    ∃ ev after next v cut,(episode p B S.program).Run (fun z=>ratBits z ≤ W) (Odd.memory native vm)
      (episodeTime p B r s n S.clock T) (Odd.memory next v) ∧ ServicePath S.serveWord before ev after ∧
      restartCount ev=cut.toNat ∧ ev.length ≤ T+1 ∧ Stored S x after (baseWidth+(T+1)*Δ) next ∧
      Ports anchor wordBase v ∧ ResultWord sign v cut := by
  let Δ:=geometricIncrement r s n e S.outputBits
  let f:=sourceReply S before
  let start:=p.initial (priceInput (2^(1+B.eval n)) anchor)
  let env:=numericalEnv S x before anchor wordBase baseWidth Δ
  let bo : WordOracle:=fun h w=>[f h w]
  let P:=fun z : ℚ=>ratBits z ≤ W
  have hz : P 0:=by change 3 ≤ W;omega
  have ho : P 1:=by change 3 ≤ W;omega
  have nativeSafe:=initial.safe height (by omega : baseWidth ≤ W) ready
  obtain ⟨m,reset,rep,portM,cleanM⟩:=resetEpoch_run p B anchor native vm ports wordRoom nativeSafe vmSafe hz ho
  have mSafe : m.AllData P:=fun j=>by simpa only [Odd.data_slot] using reset.safe_end (Odd.slot j)
  have atStart : env.cache start.transcript native := by
    change false=false ∧ Stored S x before (baseWidth+0*Δ) native
    exact ⟨rfl,by simpa using initial⟩
  have live : Live p P env start native m := ⟨rep,mSafe,nativeSafe,portM,atStart,cleanM⟩
  obtain ⟨k,hk,last,source,halt,path,wl,_,num,truth⟩:=BitEpoch.sealed_epoch anchor sign S.serveWord before pcg consistent
  have service : Handles p bo P env (eventReceipt S x before baseWidth Δ T p false)
      (eventReceipt S x before baseWidth Δ T p true) (priceHandler S.program) start last
      (transferTime r s n S.clock T) :=
    native_handles S x p anchor before (2^(1+B.eval n)) T e baseWidth wordBase W last
      (pcg f) hD hrn room height ready arg encoded matrix envelope
  obtain ⟨stop,next,v,run,produced,trace⟩:=epochLoop_run service source halt live
  have timed:=run.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.succ_le_succ hk)) 5)
  cases stop with
  | halted z =>
    obtain ⟨same,liveEnd,_⟩:=produced
    subst z
    obtain ⟨clean,stored⟩:=liveEnd.cache
    have answer:=truth clean
    have length : last.bufferRev.length=1:=by simpa using congrArg List.length answer
    obtain ⟨t,prep,finalRep,eff⟩:=preparePacket_correct liveEnd.represented liveEnd.vmSafe hz ho liveEnd.ports.send
    have guard : (Odd.cond (.addrLT nilReg statusReg)).test (Odd.memory next v)=false:=by
      rw [Odd.cond_test]
      simp [Cond.test,liveEnd.clean]
    have exposure:=(Fragment.Run.branchFalse guard (Odd.leaf .skip) (Odd.leaf_run P next liveEnd.nativeSafe prep)).mono (by rw [length] : 1+4*(13*last.bufferRev.length+7) ≤ 81)
    have known : last.transcript.length ≤ T := by
      have count:=(BitEpoch.run_follows source (.nil)).2
      change last.transcript.length ≤ 0+k at count
      omega
    have bound:=Nat.mul_le_mul_right Δ (Nat.le_trans known (Nat.le_succ T))
    have scalar : t.data (t.index sendBaseReg)=bitScalar sign := by
      rw [eff.index sendBaseReg (by decide)]
      have packet:=eff.packet
      rw [answer] at packet
      simpa using packet 0 (by simp)
    have tports:=liveEnd.ports.preserve (fun j lo _=>eff.index j (by omega))
    exact ⟨_,_,next,t,false,reset.seq (timed.seq exposure),path,by simpa [clean] using num,by omega,
      stored.mono (Nat.add_le_add_left bound _),tports,.complete finalRep.heap.nilValue ((eff.index statusReg (by decide)).trans liveEnd.clean) scalar⟩
  | request z j =>
    obtain ⟨pos,_,ns,vs,vports,nil0⟩:=produced
    obtain ⟨_,_,cut⟩:=trace.last_cut
    obtain ⟨after,stored,clean,count,hit⟩:=cut
    let a:=BitEpoch.scan S.serveWord before z.transcript
    obtain ⟨prior,priorCount,len,_⟩:=BitEpoch.scan_spec S.serveWord before z.transcript
    have followed : ServicePath S.serveWord before (a.events++[(z.bufferRev.reverse,none)]) after:=prior.append (.restart hit (.nil _))
    have exactly : restartCount (a.events++[(z.bufferRev.reverse,none)])=1:=by
      have noRestart : restartCount a.events=0:=by simpa only [clean,Bool.toNat_false] using priorCount
      exact (restartCount_append a.events [(z.bufferRev.reverse,none)]).trans (congrArg (fun k : ℕ => k+1) noRestart)
    have limit : (z.transcript.length+1)*Δ ≤ (T+1)*Δ:=Nat.mul_le_mul_right Δ (Nat.succ_le_succ count)
    have guard : (Odd.cond (.addrLT nilReg statusReg)).test (Odd.memory next v)=true:=by
      rw [Odd.cond_test]
      simp [Cond.test,nil0,pos]
    have pass:=Odd.leaf_run P next ns (Block.Eval.skip vs)
    have exposure:=(Fragment.Run.branchTrue guard pass (Odd.leaf preparePacket)).mono (by decide : 1+4*0+1 ≤ 81)
    exact ⟨_,after,next,v,true,reset.seq (timed.seq exposure),followed,exactly,by simpa using Nat.succ_le_succ (len.trans count),
      stored.mono (Nat.add_le_add_left limit _),vports,.interrupted nil0 pos⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI

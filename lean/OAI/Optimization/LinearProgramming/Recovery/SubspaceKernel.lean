import OAI.Optimization.LinearProgramming.Recovery.PhysicalRestart

/-! The marked-subspace kernel, including its real scalar sign guard. The price
learner and compressor ROMs are fixed before the row matrices; only the correctness
proof of the returned sign refers to the rational row span. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM RAM.Callable OracleSpec Contract BitRAM Geometry
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Recovery.OracleInline

private def loadChoice : Block := .seq (.op (.load 0 sendBaseReg)) (.op (.const 1 0))

noncomputable def subspaceKernel (p : BitProgram) (B : Polynomial ℕ) (minor : Program) : Fragment :=
  .seq (retry p B minor) (Odd.leaf loadChoice)

def subspaceGuard : Cond := Odd.cond (.scalarLT 1 0)

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

private theorem choice_run {P : ℚ→Prop} {next vm : Memory ℚ} (safe : (Odd.memory next vm).AllData P)
    (zero : P 0) (flag : Bool) (value : vm.data (vm.index sendBaseReg)=bitScalar flag) :
    ∃ v,(Odd.leaf loadChoice).Run P (Odd.memory next vm) 8 (Odd.memory next v) ∧
      subspaceGuard.test (Odd.memory next v)=flag := by
  have vs : vm.AllData P:=fun i=>by simpa only [Odd.data_slot] using safe (Odd.slot i)
  have ns : next.AllData P:=fun i=>by simpa only [Odd.data_even] using safe (2*i)
  let u:=vm.putData 0 (vm.data (vm.index sendBaseReg))
  let v:=u.putData 1 0
  have us : u.AllData P:=by
    intro j;by_cases h : j=0
    · subst j;simpa [u] using vs (vm.index sendBaseReg)
    · simpa [u,Memory.putData_ne _ h] using vs j
  have tip : v.AllData P:=by
    intro j;by_cases h : j=1
    · subst j;simpa [v] using zero
    · simpa [v,Memory.putData_ne _ h] using us j
  have load:=Block.Eval.op_load (safe:=Memory.AllData P) vm 0 sendBaseReg vs us
  have z:=Block.Eval.op_const (safe:=Memory.AllData P) u 1 0 us (by simpa using tip)
  refine ⟨v,Odd.leaf_run P next ns (load.seq z),?_⟩
  change (Odd.cond (.scalarLT 1 0)).test (Odd.memory next v)=flag
  rw [Odd.cond_test]
  cases flag <;> simp [Cond.test,v,u,value,bitScalar]

theorem stored_initial (S : Service D E) (x : LabelInput.Buffers r s n) (geom : Memory ℚ) (H : ℕ)
    (mat : PriceLayout.Matrices x D E geom) (safe : RowRAM.Within H geom) :
    Stored S x [] H (Odd.memory S.ready.memory geom) :=
  ⟨S.ready.memory,geom,rfl,⟨S.ready,rfl,S.live_initial⟩,mat,safe,trivial⟩

/-- Computation beginning at the actual persistent compressor initialization and
ordinary numeric matrix buffers. The terminal guard is the exact answer. -/
theorem subspaceKernel_run (S : Service D E) (x : LabelInput.Buffers r s n) (p : BitProgram) (B : Polynomial ℕ)
    (anchor : Fin n) (T e H inputBase W : ℕ) (geom vm : Memory ℚ)
    (pcg : ∀ f : Transcript→Word→Bool,p.ComputesWithin (fun h w=>[f h w]) (priceInput (2^(1+B.eval n)) anchor) T
      (pricePost (2^(1+B.eval n)) anchor)) (bits : B.eval n=S.outputBits)
    (layout : PriceLayout.Matrices x D E geom) (geomSafe : RowRAM.Within H geom)
    (ports : Ports anchor inputBase vm) (space : 3 ≤ inputBase) (vmSafe : RowRAM.Within W vm)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (orth : D * E.transpose = 0) (dim : r+s=n)
    (buffer : 256+T ≤ x.dual) (height : S.height ≤ H) (ready : RowRAM.Within S.height S.ready.memory)
    (arg : T+3 ≤ H) (encoded : T+3 ≤ e) (matrix : ∀i j,ratBits (D i j) ≤ e)
    (envelope : H+(S.restartBudget+1)*((T+1)*geometricIncrement r s n e S.outputBits) ≤ W) :
    ∃ out,(subspaceKernel p B S.program).Run (fun z=>ratBits z ≤ W)
      (Odd.memory (Odd.memory S.ready.memory geom) vm) (retryTime p B r s n S.clock T S.restartBudget+8) out ∧
      (subspaceGuard.test out=true ↔ ∃ z ∈ Submodule.span ℚ (Set.range D.row),0 ≤ z ∧ 0 < z anchor) := by
  let sign:=Service.markedSign D anchor
  have range : (2:ℕ)^(1+B.eval n)=2*(2^S.outputBits):=by rw [bits,Nat.add_comm 1 (S.outputBits),pow_succ']
  have common prior before (old : ServicePath S.serveWord [] prior before) ev after
      (path : ServicePath S.serveWord before ev after) (clean : restartCount ev=0) :
      ∃ active : Set (Fin n),∃ costs : Fin n→ℕ,anchor∈active ∧ (∀j∈active,costs j ≤ 2^(1+B.eval n)) ∧
        priceConsistent sign active costs (BitEpoch.wordHistory ev) := by
    rw [range];exact S.serveWord_clean_priceConsistent anchor hD hE orth dim prior before old ev after path clean
  obtain ⟨_,_,next,v,run,_,_,_,answer⟩:=physical_restart S x p B anchor sign T e H inputBase W S.restartBudget
    (Odd.memory S.ready.memory geom) vm pcg common S.serveWord_restartCap (stored_initial S x geom H layout geomSafe)
    ports space vmSafe hD (by omega) buffer height ready arg encoded matrix envelope
  obtain ⟨w,finish,test⟩:=choice_run (P := fun q : ℚ => ratBits q ≤ W) (next := next) (vm := v) run.safe_end (show ratBits (0:ℚ) ≤ W by change 3 ≤ W;omega) sign answer
  refine ⟨Odd.memory next w,run.seq finish,?_⟩
  rw [test];exact Service.markedSign_eq_true D anchor

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Compression.ServiceProgram
import OAI.Optimization.LinearProgramming.Compression.ServiceDecision
import OAI.Optimization.LinearProgramming.Compression.ServiceResources
import OAI.Optimization.LinearProgramming.Compression.ServiceReturn

/-! The real return-tag branch, the public success encoder and the sorted insertion
share one compiled ROM. A restart retains the newly copied row for the next request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceBranch
open RAM RAM.Callable OracleSpec.MinorLog GeneratorTable ServiceBudget ServicePrepare ServiceResources

theorem run {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (u : NonzeroPairMinor D E) {H cap : ℕ}
    {old prepared out : Memory ℚ} {last : State ℚ}
    (r : Option ℚ) (hr : r=matrixMinorRequest D E (manuscriptProxyFuel n) J u)
    (ins : Inspected D E J u H old) (ready : Ready D E J u cap old prepared)
    (ret : ServiceInvoke.Returned prepared last.memory out cap (ServiceDecision.replyTag r))
    (virtual : emits last r) (one15 : out.index 15=1) (safe : ∀ i,ratBits (out.data i) ≤ H)
    (H3 : 3 ≤ H) (count : ratBits ((J.card+1:ℕ):ℚ) ≤ H)
    (size : ∀ q,r=some q → ratBits q ≤ 3+2*onlineMinorBitPolynomial.eval n)
    (small : ∀ i ≤ 3+2*onlineMinorBitPolynomial.eval n,ratBits (i:ℚ) ≤ H)
    (room : 2*(3+2*onlineMinorBitPolynomial.eval n+2) ≤ cap) :
    ∃ t, finish.Run (fun q => ratBits q ≤ H) out (postWork n J.card+4) t ∧
      ServiceReturn.tag t=ServiceDecision.replyTag r ∧
      (∀ v,r=some v → explicitValue (t.atPC 0) v) ∧
      Persistent D E (if r.isNone then insert u J else J) H t := by
  cases r with
  | none =>
    have newKey : u∉J := by
      intro hu
      simp [matrixMinorRequest,evaluateMinorRequest,hu] at hr
    have src := ServicePost.restartSource ready ret
    obtain ⟨z,k,hk,step,stored,_,_,_⟩ := physicalRestartPost_spec ins src newKey safe
      H3 count
    obtain ⟨t,mark,tag,_,data⟩ := ServiceReturn.mark_spec false H z step.safe_end H3
    have guard : (Cond.addrLT 11 15).test out=false := by
      simp [Cond.test,ret.flag,one15,ServiceDecision.replyTag]
    have taken := Fragment.Run.branchFalse guard
      (Fragment.seq (.ofBlock restorePublishedReply) (.ofBlock (ServiceReturn.mark true)))
      ((Fragment.Run.ofBlock step).seq mark)
    refine ⟨t,taken.mono (by have hb := restart_le n J.card; omega),tag,by simp,?_⟩
    exact stored.keep (fun i _ i5 i6 => data i i5 i6) mark.safe_end
  | some q =>
    have restricted := size q rfl
    have rroom : 2*(ratBits q+2) ≤ cap := by omega
    obtain ⟨z,step,explicit,stored⟩ := ServicePost.accept ins.persistent ready ret virtual.2 safe rroom
      (fun i hi => small i (hi.trans restricted))
    obtain ⟨t,mark,tag,indices,data⟩ := ServiceReturn.mark_spec true H z step.safe_end H3
    have guard : (Cond.addrLT 11 15).test out=true := by
      simp [Cond.test,ret.flag,one15,ServiceDecision.replyTag]
    have taken := Fragment.Run.branchTrue guard ((Fragment.Run.ofBlock step).seq mark)
      (Fragment.seq (.ofBlock physicalRestartPost) (.ofBlock (ServiceReturn.mark false)))
    refine ⟨t,taken.mono (by have hb := success_le (g := J.card) restricted; omega),tag,?_,?_⟩
    · rintro v eq
      obtain rfl := Option.some.inj eq
      exact ServiceReturn.explicit_of_frame explicit indices (data 0 (by decide) (by decide))
    · exact stored.keep (fun i _ i5 i6 => data i i5 i6) mark.safe_end

end ServiceBranch
end Compression
end LinearProgramming
end Optimization
end OAI

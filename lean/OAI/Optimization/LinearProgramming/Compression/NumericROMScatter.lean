import OAI.Optimization.LinearProgramming.Compression.SignWireAddressEnvelope
import OAI.Optimization.LinearProgramming.Compression.NumericROMSetup
import OAI.Optimization.LinearProgramming.Compression.ProxyResidentInstall
import OAI.Optimization.LinearProgramming.Compression.SignWirePublicPorts

/-! Install the computed cache in the live even cells of the outer interpreter, keeping
sufficient room for every future request in the actual terminating bit computation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace NumericROM

open RAM RAM.Callable MinorProxyCache SignWire OracleSpec Polynomial

noncomputable def scatterPrefix (schedule : Polynomial ℕ) : Fragment := .seq (residentAndPorts schedule) (.ofBlock installResident)
noncomputable def scatterTime (schedule : Polynomial ℕ) : Polynomial ℕ :=
  residentPortTime schedule+100*(physicalCapBound schedule+firstResidentPolynomial+1)^2

structure Scattered (schedule : Polynomial ℕ) {g : ℕ} (n rank : ℕ) (member : Bool) (mag : Fin (g+1)→ℚ) (m : Memory ℚ) : Prop where
  ports : PublicPorts (g+2) (callbackSend (physicalCap schedule n))
    (callbackReply (g+1) (manuscriptProxyFuel n) (physicalCap schedule n))
    (callbackRow (g+1) (manuscriptProxyFuel n) (physicalCap schedule n)) (rowBase n g) m
  resident : ResidentHigh (n:=g+1) (tapeMagnitude mag) (numericProxyCacheBuffers n g)
    (manuscriptProxyFuel n) (numericCachePrecision n) (budgetC n g) (firstR n) (physicalCap schedule n)
    (rowBase n g) (fun x => ratBits x≤workingHeight schedule n mag) m
  dimension : m.index 57=n
  generators : m.index 59=g
  membership : m.index 61=member.toNat
  rankAt : m.index 63=rank
  capacity : budgetC n g≤firstR n
  code : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14)))≤firstR n
  row : rowBase n g≤firstR n

theorem scatterPrefix_run (schedule : Polynomial ℕ) {n g : ℕ} (rank : ℕ) (member : Bool) (mag : Fin (g+1)→ℚ)
    (width : g≤paperWidth n) (rank_le : rank≤g) (positive : ∀i,0<mag i) :
    ∃ t, (scatterPrefix schedule).Run (fun x => ratBits x≤workingHeight schedule n mag)
      (start [n,g,member.toNat,rank] (List.ofFn mag)).memory ((scatterTime schedule).eval n) t ∧
      Scattered schedule n rank member mag t := by
  let d := g+1
  let cap := physicalCap schedule n
  let b := rowBase n g
  let f := manuscriptProxyFuel n
  let P := fun x : ℚ => ratBits x≤workingHeight schedule n mag
  obtain ⟨logical,raw,setup,seed,support,metadata,ports,data,idx,enough,code⟩ :=
    residentAndPorts_run schedule rank member mag width rank_le positive
  have hrow := seed.callerBound 67
  rw [seed.rowPtr] at hrow
  have window := physicalCap_room schedule width b hrow
  have lived : firstR n≤cap := by dsimp only [cap];omega
  have p0 : P 0 := by
    have h := (height_dominates n (inputHeight mag) (schedule.eval n) d f (numericCachePrecision n)).2.2
    change 3≤wordComparatorBits d f (numericCachePrecision n) (queryHeight schedule n mag)
    exact (by omega : 3≤2*schedule.eval n+7).trans h
  have parity (i : ℕ) (hi : 2*cap+1< i) : raw.index (2*i)%2=0 := by
    have large : 105≤cap := by dsimp only [cap];omega
    simp [idx (2*i) (by omega),show logical.index (2*i)=0 from support.index_zero _ (by omega)]
  obtain ⟨t,k,hk,install,ready,h57,h59,h61,h63,kept⟩ := installResident_correct (tapeMagnitude mag)
    (numericProxyCacheBuffers n g) f (numericCachePrecision n) (budgetC n g) (firstR n) cap b P logical raw
    seed (by dsimp only [cap];omega) ports.window setup.safe_end p0 (fun j _ _ => congrFun data j)
    (fun j h _ => idx j h) parity
  have prev : PublicPorts (d+1) (callbackSend cap) (callbackReply d f cap) (callbackRow d f cap) b raw :=
    ⟨ports.send,ports.recv,ports.count,ports.src,ports.target⟩
  have current : PublicPorts (d+1) (callbackSend cap) (callbackReply d f cap) (callbackRow d f cap) b t := by
    apply prev.transfer
    intro j hj
    rcases hj with h|h|h|h|h <;> subst j <;> exact kept _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have combined := (setup.seq (Fragment.Run.ofBlock (P := P) install)).mono (Nat.add_le_add_left hk _)
  refine ⟨t,?_,current,ready,h57.trans metadata.dimension,h59.trans metadata.generators,h61.trans metadata.membership,
    h63.trans metadata.position,enough,code,hrow⟩
  simpa only [scatterPrefix,scatterTime,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,physicalCapBound_eval,cap,firstR] using combined

end NumericROM
end Compression
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Compression.ProxyNumericComplexity
import OAI.Optimization.LinearProgramming.RAM.Footprint

/-! A dimension-only bound on the occupied address and scalar files of a
completed ordinary numerical cache computation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable Polynomial

noncomputable def cacheSeedPolynomial : Polynomial ℕ :=
  X + (X+1)^6 + C (addressBudget (numericProxyCache.program 0)+5) + numericCacheClockPolynomial

/-- Starting with the ordinary four-header input and actual scalar magnitudes,
every occupied output register and every address word lies in the displayed
dimension-polynomial window. This also bounds the dirty numeric scratch files. -/
theorem numericCacheSeed_footprint {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (N g rank : ℕ) (member : Bool) (mag : Fin (g+1) → K) (P : K → Prop) {t : Memory K}
    (width : g≤paperWidth N) (rank_le : rank≤g)
    (run : numericProxyCache.Run P (start [N,g,member.toNat,rank] (List.ofFn mag)).memory
      (numericProxyCacheSteps N g) t) : Footprint (cacheSeedPolynomial.eval N) (t.atPC 0) := by
  let budget := addressBudget (numericProxyCache.program 0)
  let S := N + (N+1)^6 + (budget+5)
  have hg : g≤(N+1)^6 := width
  have bit : member.toNat≤1 := by cases member <;> decide
  have tape : (List.ofFn mag).length≤S := by
    rw [List.length_ofFn]
    dsimp only [S]; omega
  have dims : [N,g,member.toNat,rank].length≤S := by
    change 4≤S
    dsimp only [S]; omega
  have entries : ∀ a∈[N,g,member.toNat,rank], a≤S := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> dsimp only [S] <;> omega
  have init := Footprint.initial [N,g,member.toNat,rank] (List.ofFn mag) tape dims entries
  obtain ⟨k,hk,tr,trace,_,mem,_⟩ := Fragment.run_halt run 0
  have budget_le : addressBudget (numericProxyCache.program 0)≤S := by
    change budget≤S; dsimp only [S]; omega
  have last : Footprint (S+k) (tr (Fin.last k)) :=
    trace_footprint budget_le init trace (Fin.last k)
  have time := hk.trans (numericProxyCacheSteps_le N g width)
  have bound : S+k≤cacheSeedPolynomial.eval N := by
    simp only [cacheSeedPolynomial,eval_add,eval_pow,eval_X,eval_one,eval_C]
    exact Nat.add_le_add_left time S
  have hf := last.mono bound
  rw [← mem]
  exact ⟨hf.address,hf.data_zero,hf.index_zero⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI

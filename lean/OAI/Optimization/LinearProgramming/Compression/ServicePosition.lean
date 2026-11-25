import OAI.Optimization.LinearProgramming.Compression.NativeCache
import OAI.Optimization.LinearProgramming.Compression.ServiceTableOrder

/-! The rank counted by the physical sorted-table scan is the coordinate used by the
finite native LLL policy. This includes the rank of a repeated generator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

variable {ι : Type*} [LinearOrder ι]

theorem position_present (J : Finset ι) (u : ι) :
    (matrixMinorPosition J u).isSome.toNat=(if u∈J then 1 else 0) := by
  by_cases h : u∈J <;> simp [matrixMinorPosition,h]

theorem position_rank (J : Finset ι) (u : ι) (sorted : J.sort.Pairwise (· < ·)) :
    ∀ i, matrixMinorPosition J u=some i → i.val=rank u J.sort := by
  intro i hi
  by_cases hu : u∈J
  · simp only [matrixMinorPosition,dite_eq_left hu,Option.some.injEq] at hi
    subst i
    rw [Finset.orderIsoOfFin_symm_apply]
    obtain ⟨bound,value⟩ := membership_rank sorted (by simpa using hu)
    let j : Fin J.sort.length := ⟨rank u J.sort,bound⟩
    calc
      J.sort.idxOf u = J.sort.idxOf J.sort[j.val] := congrArg (fun v => J.sort.idxOf v) value.symm
      _ = j.val := sorted.nodup.idxOf_getElem j.val j.isLt
  · simp [matrixMinorPosition,hu] at hi

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI

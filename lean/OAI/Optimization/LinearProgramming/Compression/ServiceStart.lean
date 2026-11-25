import OAI.Optimization.LinearProgramming.Compression.ServiceInit
import OAI.Optimization.LinearProgramming.RAM.TapeBits

/-! The fixed initializer at the public input convention. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog

def minorServiceInitProgram : RAM.Program := minorServiceInitBlock.compile 0 ++ [.halt 0]

private theorem minorEntry_length {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℚ) :
    (entries A).length = d*n := by
  simp [entries, List.length_flatten, List.map_ofFn, List.sum_ofFn]

/-- Values stored here must still be available after any subsequent call to `resume`. -/
structure MinorServiceInputFrame (d e n : ℕ) (input : List ℚ) (s : RAM.State ℚ) : Prop where
  firstRows : s.data 1 = d
  lastRows : s.data 2 = e
  columns : s.data 3 = n
  emptyGenerators : s.data 4 = 0
  entry : ∀ j < n*n, s.data (7+j)=input[j]?.getD 0

theorem MinorServiceInputFrame.resume {d e n : ℕ} {input : List ℚ} {s : RAM.State ℚ}
    (h : MinorServiceInputFrame d e n input s) (words : List ℕ) :
    MinorServiceInputFrame d e n input (OracleSpec.MinorLog.resume s words) :=
  ⟨h.firstRows,h.lastRows,h.columns,h.emptyGenerators,h.entry⟩

/-- From the sealed matrix tape this program prepares the persistent scalar header and
an unmodified, row-major copy of both matrices. The clock counts the final halt and
all temporary values obey the stated input-length bound. -/
theorem minorServiceInit_call {d e n : ℕ} (hn : d+e=n) (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) :
    let input := entries D ++ entries E
    ∃ ready, call minorServiceInitProgram (50*(n+1)^2) (4*(totalBits input+1))
        (start [d,e,n] input) ready ∧ ready.output=some 0 ∧
      MinorServiceInputFrame d e n input ready := by
  let input := entries D ++ entries E
  let L := totalBits input
  let H := 4*(L+1)
  have linput : input.length=n*n := by simp [input,minorEntry_length,← Nat.add_mul,hn]
  have hnL : n ≤ L := (Nat.le_mul_self n).trans (linput ▸ entry_count_le_totalBits input)
  have hsmall {q : ℚ} (hq : RAM.ratBits q ≤ L) : RAM.ratBits q ≤ H := by dsimp [H]; omega
  have h0 : 3 ≤ H := by dsimp [H]; omega
  have hnat (j : ℕ) (hj : j ≤ n) : ratBits (j : ℚ) ≤ H := by
    simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
    change 3 + j.log2 + 0 ≤ H
    have hlog := Nat.log2_le_self j
    dsimp [H]; omega
  have h1 : ratBits (1 : ℚ) ≤ H := h0
  have hs (i : ℕ) : ratBits (input[i]?.getD 0) ≤ H := by
    cases h : input[i]? with
    | none => exact h0
    | some q => exact hsmall (member_bits_le_totalBits (List.mem_of_getElem? h))
  obtain ⟨m,hm,hd,he,hc,hj,hentries⟩ := minorServiceInitBlock_spec (fun q => ratBits q ≤ H)
    input d e n hn hs h1 hnat
  obtain ⟨tr,ht,ho,hmem,hbits⟩ := hm.halted_trace (tag := 0)
  have hk := minorServiceInitCost_le hn
  let last := tr (Fin.last (minorServiceInitCost d e n+1))
  have eqMem : last.memory=m := hmem
  have out (j : ℕ) : last.data j=m.data j := congrFun (congrArg Memory.data eqMem) j
  refine ⟨last, ⟨_,hk,tr,ht,rfl,hbits⟩, ho, ?_⟩
  exact ⟨(out 1).trans hd,(out 2).trans he,(out 3).trans hc,(out 4).trans hj,
    fun j hj => (out _).trans (hentries _ hj)⟩

end Compression
end LinearProgramming
end Optimization
end OAI

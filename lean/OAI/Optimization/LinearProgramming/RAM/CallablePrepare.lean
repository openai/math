import OAI.Optimization.LinearProgramming.RAM.CallablePrepareHigh
import OAI.Optimization.LinearProgramming.RAM.CallablePrepareLow
import OAI.Optimization.LinearProgramming.RAM.CallableRawTapes
import OAI.Optimization.LinearProgramming.RAM.Footprint

/-! Preparation of an arbitrary ordinary native input from two arrays in a live caller.
The same fixed block handles short, empty and shrinking tapes, including clearing any
remaining cells from the previous invocation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

def prepareInputs : Block := .seq prepareHigh prepareLow

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem prepareInputs_spec (m : Memory K) (sb ab B : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hs : m.AllData P) (hz : P 0)
    (hxs : xs.length≤B) (hdims : dims.length≤B)
    (tail : ∀ q, B≤q → m.data (2*q)=0 ∧ m.index (2*q)=0) :
    ∃ t k, k ≤ 19*B+225 ∧ Block.Eval (Memory.AllData P) prepareInputs m k t ∧
      OddFrame m t ∧ ∀ q, entryReady t xs dims q := by
  obtain ⟨s,i,hi,ei,fs,high⟩ := prepareHigh_spec m sb ab B xs dims src hs hz hxs hdims tail
  obtain ⟨t,j,hj,ej,ft,low,keep⟩ := prepareLow_spec s sb ab B xs dims (src.ofOdd fs) ei.safe_end hz
  refine ⟨t,i+j,by omega,ei.seq ej,fs.trans ft,?_⟩
  intro q
  by_cases hq : q<5
  · exact low q hq
  · obtain ⟨hd,ha⟩ := high q (by omega)
    obtain ⟨pd,pa⟩ := keep q (by omega)
    exact ⟨pd.trans hd,pa.trans ha⟩

/-- The final even bank agrees on *every* register with a native machine start.
In particular this block composes directly with the inlining theorem for any
native subprogram. The old, possibly dirty callee bank needs only its proven
finite footprint; no old cell values are assumed inside that footprint. -/
theorem prepareInputs_native (old : State K) (caller : Memory K) (sb ab C B : ℕ)
    (xs : List K) (dims : List ℕ)
    (raw : RawTapes caller sb ab B xs dims) (hs : caller.AllData P)
    (ho : old.memory.AllData P) (hz : P 0) (foot : Footprint C old) (hCB : C<B)
    (hxs : xs.length≤B) (hdims : dims.length≤B) :
    ∃ k ≤ 19*B+225, Block.Eval (Memory.AllData P) prepareInputs
      (Odd.memory old.memory caller) k (Odd.memory ((start dims xs).memory) caller) := by
  obtain ⟨t,k,hk,ev,fr,all⟩ := prepareInputs_spec (Odd.memory old.memory caller) sb ab B
    xs dims (raw.source old.memory) (Odd.allData _ _ ho hs) hz hxs hdims (by
      intro q hq
      rw [Odd.data_even,Odd.index_even]
      change old.data q=0 ∧ 2*old.index q=0
      rw [foot.data_zero q (by omega),foot.index_zero q (by omega)]
      simp)
  rw [nativeMemory_of_entryReady old.memory caller t xs dims fr all] at ev
  exact ⟨k,hk,ev⟩

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

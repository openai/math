import OAI.Optimization.LinearProgramming.BitRAM.DispatchFrame
import OAI.Optimization.LinearProgramming.BitRAM.DispatchResumable

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open RAM RAM.Tape OracleSpec
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def cacheFrame (p : BitProgram) (P : K → Prop) : PrefixFrame p P where
  rel a t := StableHeaders a t ∧ StableEven a t
  refl _ := ⟨fun _ _ _ => rfl,fun _ _ _ => rfl⟩
  trans ab bc := ⟨fun i lo hi => (bc.1 i lo hi).trans (ab.1 i lo hi),
    fun i lo even => (bc.2 i lo even).trans (ab.2 i lo even)⟩
  limit m v := ⟨fun _ lo _ => Memory.putIndex_ne _ (by unfold limitReg; omega) _,
    fun _ lo _ => Memory.putIndex_ne _ (by unfold limitReg; omega) _⟩
  table := fun {c q m} pc r g => issuedTable_complete_frame (p := p) (c := c) (q := q) (m := m) pc r g

theorem runUntilRequest_complete_frame {p : BitProgram} {c : p.Config} {n : ℕ} {stop : Stop p}
    (pre : Prefix p c n stop) {P : K → Prop} {m : Memory K} (rep : Rep p c m) (safe : Good P m) :
    ∃ t k, k ≤ (2*p.states+35)*(n+1)+2 ∧ Block.Eval (Good P) (runUntilRequest p) m k t ∧
      stop.represented t ∧ t.data=m.data ∧ StableHeaders m t ∧ StableEven m t :=
  by simpa only [cacheFrame] using runUntilRequest_with_frame (cacheFrame p P) pre rep safe

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI

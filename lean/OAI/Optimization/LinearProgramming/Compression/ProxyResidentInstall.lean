import OAI.Optimization.LinearProgramming.Compression.ProxyResidentInstallCore
import OAI.Optimization.LinearProgramming.Compression.ProxyResidentLayout

/-! Native installation of the finite ordinary cache into the resident numerical RAM. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM MinorProxyCache ResidentInstall

/-- A complete native installation from an actual ordinary allocated cache. Physical
odd control ports survive, the metadata is published unencoded, and every intermediate
scalar belongs to the same input predicate. -/
theorem installResident_correct {n : ℕ} (mag : ℕ→ℚ) (L : Buffers)
    (fuel prec C R cap base : ℕ) (P : ℚ→Prop) (caller raw : Memory ℚ)
    (seed : ResidentNumeric (n:=n) mag L fuel prec C R base P zeroResidentNative caller)
    (hcap : 105 ≤ cap) (inputCap : raw.index 0 = cap) (safe : raw.AllData P) (zero : P 0)
    (data : ∀ j, 16≤j → j≤cap → raw.data j = caller.data j)
    (address : ∀ j, 60≤j → j≤cap → raw.index j = caller.index j)
    (tail : ∀ i, 2*cap+1 < i → raw.index (2*i)%2 = 0) :
    ∃ t k, k ≤ 100*(cap+R+1)^2 ∧ Block.Eval (Memory.AllData P) installResident raw k t ∧
      ResidentHigh (n:=n) mag L fuel prec C R cap base P t ∧
      t.index 57 = caller.index 102 ∧ t.index 59 = caller.index 103 ∧
      t.index 61 = caller.index 104 ∧ t.index 63 = caller.index 105 ∧
      ∀ j, 16≤j → j%2=1 → j≠57 → j≠59 → j≠61 → j≠63 → t.index j = raw.index j := by
  obtain ⟨t,k,time,run,pair,outside,metadata,frame⟩ :=
    installResident_frames P caller raw R cap seed.callerBound hcap inputCap safe zero data address tail
  have high := highShell_from_scatter seed
    (fun j lo hi => (pair j lo hi).innerData) (fun j lo hi => (pair j lo hi).innerIndex)
    (fun j lo hi => (pair j lo hi).outerData) (fun j lo hi => (pair j lo hi).outerIndex) outside
  exact ⟨t,k,time,run,high.restrict (by omega),metadata 0 (by decide),metadata 1 (by decide),
    metadata 2 (by decide),metadata 3 (by decide),frame⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import OAI.Optimization.LinearProgramming.BitRAM.Ops

/-! The shared physical register invariant for numeric service callbacks over
arbitrary scalar types. Only the reserved high even cells carry persistent data. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable

/-- Physical even words above the low scratch region encode a window of the
nested memory. The next query row may overwrite its own destination. -/
structure HighShell {K : Type*} (raw old caller : Memory K) (cap base p : ℕ) : Prop where
  data : ∀ i, 32≤ i → i≤cap → (∀ j<p, 2*i≠4*(base+j)+2) →
    raw.data (2*i)=(Odd.memory old caller).data i
  index : ∀ i, 32≤ i → i≤cap → raw.index (2*i)=2*(Odd.memory old caller).index i
  highParity : ∀ i, 32≤ i → raw.index (2*i)%2=0

theorem HighShell.transfer {K : Type*} {raw t old caller : Memory K} {cap base p : ℕ}
    (h : HighShell raw old caller cap base p)
    (data : ∀ i, 32≤ i → i≤cap → (∀ j<p, 2*i≠4*(base+j)+2) → t.data (2*i)=raw.data (2*i))
    (index : ∀ i, 32≤ i → t.index (2*i)=raw.index (2*i)) : HighShell t old caller cap base p :=
  ⟨fun i hi hc exc => (data i hi hc exc).trans (h.data i hi hc exc),
   fun i hi hc => (index i hi).trans (h.index i hi hc),
   fun i hi => by rw [index i hi]; exact h.highParity i hi⟩

theorem HighShell.ofFrame {K : Type*} {raw t old caller : Memory K} {cap base p : ℕ}
    (h : HighShell raw old caller cap base p) (data : t.data=raw.data) (even : BitRAM.StableEven raw t) :
    HighShell t old caller cap base p :=
  h.transfer (fun i _ _ _ => congrFun data (2*i)) (fun i hi => even (2*i) (by omega) (by omega))

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI

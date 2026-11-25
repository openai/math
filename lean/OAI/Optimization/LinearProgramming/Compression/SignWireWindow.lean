import OAI.Optimization.LinearProgramming.Compression.SignWireInvoke
import OAI.Optimization.LinearProgramming.RAM.CallableLocalFrame

/-! A finite allocated numerical window coexists with a live outer VM. Its
other even cells and its entire odd frame contain arbitrary caller data. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable

/-- The actual even bank agrees with the inner numerical state on this
finite prefix. Address words in the outer even bank encode doubled numbers. -/
def WindowImage {K : Type*} (physical : Memory K) (cap : ℕ) (virtual : Memory K) : Prop :=
  ∀ i ≤ cap, physical.data (2*i)=virtual.data i ∧ physical.index (2*i)=2*virtual.index i

def EvenParity {K : Type*} (m : Memory K) : Prop := ∀ i, m.index (2*i)%2=0

def evenView {K : Type*} (m : Memory K) : Memory K :=
  ⟨fun i => m.data (2*i),fun i => m.index (2*i)/2⟩

theorem WindowImage.reconstruct {K : Type*} {m v : Memory K} {cap : ℕ}
    (image : WindowImage m cap v) (parity : EvenParity m) :
    m=Call.pack (windowMemory cap (evenView m) v) (Call.savedOddFrame m) := by
  apply Call.eq_pack_of_even
  · intro i
    by_cases h : i ≤ cap
    · simpa [windowMemory,h] using (image i h).1
    · simp [windowMemory,h,evenView]
  · intro i
    by_cases h : i ≤ cap
    · simpa [windowMemory,h] using (image i h).2
    · simp only [windowMemory,h,ite_false,evenView]
      have := parity i
      omega

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The physical state outside the finite callee window survives the native
execution. This includes arbitrary live scalar data backed by the bit-packet
area and the register-index memory of the outer BitRAM heap. -/
theorem isolatedSign_window_run {f : Fragment} {P : K → Prop} {s t physical : Memory K}
    {B b cap : ℕ} (run : f.Run P s B t) (o : Ordering) (tag : t.index 29=2*comparisonTag o+1)
    (raw : WindowImage physical cap s) (parity : EvenParity physical) (safe : physical.AllData P)
    (prog : addressBudget (tagReturningProgram f) ≤ b) (init : ∀ j,s.index j ≤ b) (space : b+(B+5) ≤ cap) :
    let final := windowMemory cap (evenView physical) ((t.putIndex 0 3).putIndex 2 5)
    (isolatedSign f).Run P physical (2*(B+5)+2)
      ((Call.pack final (Call.savedOddFrame physical)).putIndex 14 (comparisonTag o)) := by
  obtain ⟨k,hk,tr,ht,ho,he,hgood⟩ := tagReturningProgram_trace_memory run o tag
  let ext := evenView physical
  let frame := Call.savedOddFrame physical
  let tr' (i : Fin (k+1)) := windowState cap ext (tr i)
  have native : Trace (tagReturningProgram f) ((windowMemory cap ext s).atPC 0) k tr' :=
    trace_windowState ext prog init ht (by omega)
  have last : (tr' (Fin.last k)).memory=windowMemory cap ext ((t.putIndex 0 3).putIndex 2 5) := by
    change windowMemory cap ext (tr (Fin.last k)).memory=_
    rw [he]
  have hs : frame.AllData P := fun i => safe (2*i+1)
  have data (i : Fin (k+1)) (j : ℕ) : P ((tr' i).data j) := by
    change P (if j ≤ cap then (tr i).data j else physical.data (2*j))
    split_ifs <;> first | exact hgood i j | exact safe _
  have call := invokeTag14_trace _ P (windowMemory cap ext s) frame tr' (by cases o <;> decide)
    native data hs (show (tr' (Fin.last k)).output=some (comparisonTag o) from ho)
  rw [last] at call
  have start : physical = Call.pack (windowMemory cap ext s) frame := raw.reconstruct parity
  rw [← start] at call
  exact call.mono (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hk) 2)

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI

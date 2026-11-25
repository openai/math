import OAI.Optimization.LinearProgramming.RAM.CallablePrepareBase
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase

/-! Ordinary native input tapes staged as two logical arrays in a live caller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

/-- Obligations for a front end that has emitted scalar and address words to a
pair of contiguous logical arrays. The words are ordinary natural addresses. -/
structure RawTapes {K : Type*} (m : Memory K) (sb ab B : ℕ) (xs : List K) (dims : List ℕ) : Prop where
  scalarBase : m.index 55 = sb
  scalarLength : m.index 56 = xs.length
  addressBase : m.index 57 = ab
  addressLength : m.index 58 = dims.length
  bound : m.index 60 = B
  scalarAt : ∀ j (h : j<xs.length), m.data (sb+j)=xs[j]
  addressAt : ∀ j (h : j<dims.length), m.index (ab+j)=dims[j]

theorem RawTapes.source {K : Type*} {sb ab B : ℕ} {xs : List K} {dims : List ℕ}
    {caller : Memory K} (raw : RawTapes caller sb ab B xs dims) (callee : Memory K) :
    PrepareSource (Odd.memory callee caller) sb ab B xs dims := by
  constructor
  · change (Odd.memory callee caller).index (Odd.slot 55)=Odd.slot sb
    rw [Odd.index_slot,raw.scalarBase]
  · change (Odd.memory callee caller).index (Odd.slot 56)=Odd.slot xs.length
    rw [Odd.index_slot,raw.scalarLength]
  · change (Odd.memory callee caller).index (Odd.slot 57)=Odd.slot ab
    rw [Odd.index_slot,raw.addressBase]
  · change (Odd.memory callee caller).index (Odd.slot 58)=Odd.slot dims.length
    rw [Odd.index_slot,raw.addressLength]
  · change (Odd.memory callee caller).index (Odd.slot 60)=Odd.slot B
    rw [Odd.index_slot,raw.bound]
  · intro i hi
    change (Odd.memory callee caller).data (Odd.slot (sb+i))=xs[i]
    rw [Odd.data_slot, raw.scalarAt i hi]
  · intro i hi
    change (Odd.memory callee caller).index (Odd.slot (ab+i))=Odd.slot dims[i]
    rw [Odd.index_slot,raw.addressAt i hi]

/-- The header lies outside the address array whose words are being staged. Scalar
payloads use the independent scalar register bank. -/
theorem RawTapes.setBound {K : Type*} {m : Memory K} {sb ab C : ℕ} {xs : List K} {dims : List ℕ}
    (h : RawTapes m sb ab C xs dims) (B : ℕ) (disjoint : ∀ j<dims.length, ab+j≠60) :
    RawTapes (m.putIndex 60 B) sb ab B xs dims := by
  refine ⟨?_,?_,?_,?_,Memory.putIndex_same ..,h.scalarAt,?_⟩
  · simpa using h.scalarBase
  · simpa using h.scalarLength
  · simpa using h.addressBase
  · simpa using h.addressLength
  · intro j hj
    rw [Memory.putIndex_ne _ (disjoint j hj)]
    exact h.addressAt j hj

private theorem sameMemory {F : Type*} {m n : Memory F}
    (hd : ∀ i, m.data i = n.data i) (hi : ∀ i, m.index i = n.index i) : m=n := by
  cases m; cases n
  congr <;> funext i
  · exact hd i
  · exact hi i

theorem nativeMemory_of_entryReady {K : Type*} [Zero K] (old caller t : Memory K) (xs : List K) (dims : List ℕ)
    (frame : OddFrame (Odd.memory old caller) t) (ready : ∀ j, t.data (2*j)=xs[j]?.getD 0 ∧ t.index (2*j)=2*(dims[j]?.getD 0)) :
    t=Odd.memory ((start dims xs).memory) caller := by
  apply sameMemory
  · intro i
    by_cases h : i%2=0
    · have eq : 2*(i/2)=i := by omega
      rw [← eq,Odd.data_even]
      exact (ready (i/2)).1
    · have eq : Odd.slot (i/2)=i := by dsimp [Odd.slot]; omega
      rw [← eq,Odd.data_slot]
      exact (frame.data (i/2)).trans (Odd.data_slot old caller _)
  · intro i
    by_cases h : i%2=0
    · have eq : 2*(i/2)=i := by omega
      rw [← eq,Odd.index_even]
      exact (ready (i/2)).2
    · have eq : Odd.slot (i/2)=i := by dsimp [Odd.slot]; omega
      rw [← eq,Odd.index_slot]
      exact (frame.index (i/2)).trans (Odd.index_slot old caller _)

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

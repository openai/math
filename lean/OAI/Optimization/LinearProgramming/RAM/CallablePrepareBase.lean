import OAI.Optimization.LinearProgramming.RAM.Array

/-! Shared layout for initializing a callee on the even register bank without overwriting
the caller on the odd bank. Each logical address stored in the caller is an odd address. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

/-- All occupied and unoccupied logical caller cells retain their original contents. -/
structure OddFrame {K : Type*} (m t : Memory K) : Prop where
  data : ∀ j, t.data (2*j+1) = m.data (2*j+1)
  index : ∀ j, t.index (2*j+1) = m.index (2*j+1)

namespace OddFrame
variable {K : Type*}

theorem refl (m : Memory K) : OddFrame m m := ⟨fun _ => rfl, fun _ => rfl⟩

theorem trans {m t u : Memory K} (h : OddFrame m t) (g : OddFrame t u) : OddFrame m u :=
  ⟨fun j => (g.data j).trans (h.data j), fun j => (g.index j).trans (h.index j)⟩

theorem putData {m t : Memory K} (h : OddFrame m t) (d : ℕ) (v : K) :
    OddFrame m (t.putData (2*d) v) := by
  refine ⟨?_, h.index⟩
  intro j
  rw [Memory.putData_ne _ (by omega : 2*j+1 ≠ 2*d)]
  exact h.data j

theorem putIndex {m t : Memory K} (h : OddFrame m t) (d v : ℕ) :
    OddFrame m (t.putIndex (2*d) v) := by
  refine ⟨h.data, ?_⟩
  intro j
  rw [Memory.putIndex_ne _ (by omega : 2*j+1 ≠ 2*d)]
  exact h.index j
end OddFrame

/-- Logical caller slots 55--58 provide the scalar and address tape descriptors.
Slot 60 bounds the old even-bank footprint and both new lengths. All stored caller
address values are represented by `2*v+1`, including the elements of the address tape. -/
structure PrepareSource {K : Type*} (m : Memory K) (sb ab B : ℕ) (xs : List K) (dims : List ℕ) : Prop where
  scalarBase : m.index 111 = 2*sb+1
  scalarLength : m.index 113 = 2*xs.length+1
  addressBase : m.index 115 = 2*ab+1
  addressLength : m.index 117 = 2*dims.length+1
  bound : m.index 121 = 2*B+1
  scalarAt : ∀ j (h : j<xs.length), m.data (2*(sb+j)+1) = xs[j]
  addressAt : ∀ j (h : j<dims.length), m.index (2*(ab+j)+1) = 2*dims[j]+1

theorem PrepareSource.ofOdd {K : Type*} {m t : Memory K} {sb ab B : ℕ} {xs : List K} {dims : List ℕ}
    (s : PrepareSource m sb ab B xs dims) (h : OddFrame m t) : PrepareSource t sb ab B xs dims :=
  ⟨(h.index 55).trans s.scalarBase, (h.index 56).trans s.scalarLength,
   (h.index 57).trans s.addressBase, (h.index 58).trans s.addressLength,
   (h.index 60).trans s.bound, fun j hj => (h.data (sb+j)).trans (s.scalarAt j hj),
   fun j hj => (h.index (ab+j)).trans (s.addressAt j hj)⟩

/-- A compile-time constant displacement is charged one concrete `incr` per unit. -/
def bumpIndex (r : ℕ) : ℕ → Block
  | 0 => .skip
  | k+1 => .seq (bumpIndex r k) (.op (.incr r r))

def copyIndexPlus (dst src k : ℕ) : Block := .seq (.op (.addrCopy dst src)) (bumpIndex dst k)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem bumpIndex_spec (m : Memory K) (r k : ℕ) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) (bumpIndex r k) m k (m.putIndex r (m.index r+k)) := by
  induction k with
  | zero =>
    have eq : m.putIndex r (m.index r+0) = m := by cases m; simp [Memory.putIndex]
    rw [eq]; exact .skip h
  | succ k ih =>
    let u := m.putIndex r (m.index r+k)
    have hu : u.AllData P := h
    have inc := Block.Eval.op_incr (safe := Memory.AllData P) u r r hu hu
    have eq : u.putIndex r (u.index r+1) = m.putIndex r (m.index r+(k+1)) := by
      simp [u,Memory.putIndex,Function.update_idem,Nat.add_assoc]
    rw [← eq]; exact ih.seq inc

theorem copyIndexPlus_spec (m : Memory K) (dst src k : ℕ) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) (copyIndexPlus dst src k) m (1+k)
      (m.putIndex dst (m.index src+k)) := by
  let u := m.putIndex dst (m.index src)
  have hu : u.AllData P := h
  have e₁ := Block.Eval.op_addrCopy (safe := Memory.AllData P) m dst src h hu
  have e₂ := bumpIndex_spec u dst k hu
  have eq : u.putIndex dst (u.index dst+k) = m.putIndex dst (m.index src+k) := by
    simp [u,Memory.putIndex,Function.update_idem]
  rw [← eq]; exact e₁.seq e₂

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI

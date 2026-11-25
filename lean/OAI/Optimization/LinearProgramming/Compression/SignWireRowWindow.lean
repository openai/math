import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import OAI.Optimization.LinearProgramming.Compression.SignWireOuterStage
import OAI.Optimization.LinearProgramming.Compression.SignWireWindow
import Mathlib.Algebra.Ring.Parity

/-! Reconstruct the logical numeric caller from the migrated signed query row inside
a finite even-bank window. The outer VM may keep arbitrary data in the exterior. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable

def writeRow {K : Type*} {p : ℕ} (m : Memory K) (base : ℕ) (row : Fin p → K) : Memory K where
  data i := if h : base≤ i ∧ i<base+p then row ⟨i-base,by omega⟩ else m.data i
  index := m.index

@[simp] theorem writeRow_index {K : Type*} {p : ℕ} (m : Memory K) (base : ℕ) (row : Fin p → K) :
    (writeRow m base row).index=m.index := rfl

theorem writeRow_hit {K : Type*} {p : ℕ} (m : Memory K) (base : ℕ) (row : Fin p → K)
    (i : ℕ) (h : base≤ i ∧ i<base+p) :
    (writeRow m base row).data i=row ⟨i-base,by omega⟩ := by simp [writeRow,h]

theorem writeRow_at {K : Type*} {p : ℕ} (m : Memory K) (base : ℕ) (row : Fin p → K) (i : Fin p) :
    (writeRow m base row).data (base+i.val)=row i := by
  have hi : base≤base+i.val ∧ base+i.val<base+p := by omega
  have key : (⟨base+i.val-base,by omega⟩ : Fin p)=i := Fin.ext (by simp)
  exact (writeRow_hit m base row _ hi).trans (congrArg row key)

theorem writeRow_miss {K : Type*} {p : ℕ} (m : Memory K) (base : ℕ) (row : Fin p → K)
    (i : ℕ) (h : ¬(base≤ i ∧ i<base+p)) :
    (writeRow m base row).data i=m.data i := by simp [writeRow,h]

theorem writeRow_allData {K : Type*} {p : ℕ} {P : K → Prop} {m : Memory K}
    (base : ℕ) {row : Fin p → K} (hm : m.AllData P) (hr : ∀ i, P (row i)) :
    (writeRow m base row).AllData P := by
  intro i
  by_cases h : base≤ i ∧ i<base+p
  · rw [writeRow_hit _ _ _ _ h]
    exact hr _
  · rw [writeRow_miss _ _ _ _ h]
    exact hm i

/-- The pre-stage representation only constrains live scalars inside the reserved
window. The destination row and the low scalar scratch are allowed to be dirty. -/
structure RowWindowSetup {K : Type*} (raw old caller : Memory K) (cap base p : ℕ) : Prop where
  data : ∀ i≤cap, i≠0 → (∀ j<p, 2*i≠4*(base+j)+2) → raw.data (2*i)=(Odd.memory old caller).data i
  index : ∀ i≤cap, 32≤ i → raw.index (2*i)=2*(Odd.memory old caller).index i
  nativeLow : ∀ j<16, old.index j=0
  callerLow : ∀ j<16, caller.index j=0
  highParity : ∀ i, 32≤ i → raw.index (2*i)%2=0

/-- The scalar zero used by the scatter belongs to the virtual native memory,
so its established size and address footprint are retained after reconstruction. -/
theorem footprint_scratchZero {K : Type*} [Zero K] {old : Memory K} {C : ℕ}
    (h : Footprint C (old.atPC 0)) (x : K) :
    Footprint C ((old.putData 0 x).atPC 0) := by
  refine ⟨h.address,?_,h.index_zero⟩
  intro i hi
  exact (Memory.putData_ne old (by omega : i≠0) x).trans (h.data_zero i hi)

namespace OuterRowStaged

variable {K : Type*} {m t old caller : Memory K} {cap src base p : ℕ}

theorem windowData (st : OuterRowStaged m t src base p) (h : RowWindowSetup m old caller cap base p)
    (row : Fin p → K) (words : ∀ i : Fin p, m.data (src+i.val)=row i) (i : ℕ) (hi : i≤cap) :
    t.data (2*i)=(Odd.memory (old.putData 0 (t.data 0)) (writeRow caller base row)).data i := by
  obtain ⟨j, rfl|rfl⟩ : ∃ j, i=2*j ∨ i=Odd.slot j := Nat.even_or_odd' i
  · rw [Odd.data_even]
    by_cases z : j=0
    · subst j
      simp
    · have outside : ∀ k<p, 2*(2*j)≠4*(base+k)+2 := fun k _ => by omega
      rw [Memory.putData_ne _ z]
      exact (st.scalars _ (by omega) outside).trans
        (by simpa only [Odd.data_even] using h.data (2*j) hi (by omega) outside)
  · rw [Odd.data_slot]
    by_cases hit : base≤j ∧ j<base+p
    · let k : Fin p := ⟨j-base,by omega⟩
      have eq : base+k.val=j := by dsimp only [k]; omega
      have addr : 2*Odd.slot j=4*(base+k.val)+2 := by rw [eq]; unfold Odd.slot; omega
      rw [addr,writeRow_hit _ _ _ _ hit]
      exact (st.words k.val k.isLt).trans (words k)
    · have outside : ∀ k<p, 2*Odd.slot j≠4*(base+k)+2 := by
        intro k hk
        unfold Odd.slot
        omega
      have nz : Odd.slot j≠0 := by unfold Odd.slot; omega
      rw [writeRow_miss _ _ _ _ hit]
      exact (st.scalars _ (by omega) outside).trans
        (by simpa only [Odd.data_slot] using h.data (Odd.slot j) hi nz outside)

theorem windowIndex (st : OuterRowStaged m t src base p) (h : RowWindowSetup m old caller cap base p)
    (i : ℕ) (hi : i≤cap) : t.index (2*i)=2*(Odd.memory old caller).index i := by
  by_cases big : 32≤ i
  · exact (st.high _ (by omega)).trans (h.index i hi big)
  obtain ⟨j, rfl|rfl⟩ : ∃ j, i=2*j ∨ i=Odd.slot j := Nat.even_or_odd' i
  · have hj : j<16 := by omega
    calc
      t.index (2*(2*j)) = 0 := by simpa only [show 2*(2*j)=4*j by omega] using st.lowNative j hj
      _ = 2*(Odd.memory old caller).index (2*j) := by simp [h.nativeLow j hj]
  · have hj : j<16 := by unfold Odd.slot at big; omega
    calc
      t.index (2*Odd.slot j) = 2 := by
        simpa only [show 2*Odd.slot j=4*j+2 by unfold Odd.slot; omega] using st.lowCaller j hj
      _ = 2*(Odd.memory old caller).index (Odd.slot j) := by
        simpa only [Odd.index_slot,h.callerLow j hj] using (show (2 : ℕ) = 2*Odd.slot 0 from rfl)

theorem parity (st : OuterRowStaged m t src base p) (hp : ∀ i, 32≤ i → m.index (2*i)%2=0) :
    EvenParity t := by
  intro i
  by_cases big : 32≤ i
  · rw [st.high _ (by omega)]
    exact hp i big
  · rw [st.indices]
    split_ifs <;> omega

/-- A complete image of the nested numeric memory for the finite physical window,
including global outer-even parity. No source scalar outside the window is restricted. -/
theorem window_image (st : OuterRowStaged m t src base p) (h : RowWindowSetup m old caller cap base p)
    (row : Fin p → K) (words : ∀ i : Fin p, m.data (src+i.val)=row i) :
    WindowImage t cap (Odd.memory (old.putData 0 (t.data 0)) (writeRow caller base row)) ∧ EvenParity t := by
  refine ⟨fun i hi => ⟨st.windowData h row words i hi,?_⟩,st.parity h.highParity⟩
  exact st.windowIndex h i hi

end OuterRowStaged
end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
